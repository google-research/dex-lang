#include <assert.h>
#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdatomic.h>
#include <stdbool.h>

// A work-stealing scheduler is described in
// Robert D. Blumofe, Christopher F. Joerg, Bradley C. Kuszmaul, Charles E. Leiserson, Keith H.
// Randall, and Yuli Zhou. Cilk: An efficient multithreaded runtime system. In Proceedings
// of the Fifth ACM SIGPLAN Symposium on Principles and Practice of Paral lel Programming
// (PPoPP), pages 207{216, Santa Barbara, California, July 1995.
// http://supertech.csail.mit.edu/papers/PPoPP95.pdf

// However, that refers to an outdated model of Cilk; an update appears in
// Essential idea of work stealing mentioned in Leiserson and Platt,
// Programming Parallel Applications in Cilk

struct Work;

// A Task is a function pointer that consumes a Work* and returns a Work*.
// The input `Work` is always a pointer to the Work struct containing that
// Task, which it accepts in order to be able to deallocate it.
// Question: Do we also want to tell the task the thread id of the worker
// that's running it?  Maybe to support thread-local accumulators for
// commutative reductions?
// Oh yeah, also to know which worker's queue to put more stuff onto.
//
// The return value is a trampoline: a `Task` returns the next work to do, if
// it's runnable, or NULL if there isn't one.
//
// `Task`s are internal to the work-stealing system; the client does not
// provide or consume `Task`s.
typedef struct Work* (*Task)(int thread_id, struct Work*);

typedef struct Work {
  Task task;
  atomic_int join_count;
  void* args[];
} Work;

Work* EMPTY = (Work*)-1;
Work* ABORT = (Work*)-2;

/////////////////////////
// Work-stealing deque //
/////////////////////////

// Code adapted from https://fzn.fr/readings/ppopp13.pdf

typedef struct {
  atomic_size_t size;
  Work* buffer[];
} Array;

typedef struct {
  // These should be 64-bit so they never overflow
  atomic_size_t top, bottom;
  _Atomic(Array *) array;
} Deque;

void init(Deque* q, size_t size_hint) {
  // This does not appear in https://fzn.fr/readings/ppopp13.pdf; I am imputing
  // it.
  // Initialize the buffer indices at 1 to prevent underflow.  The buffer
  // indices are of type `size_t`; the top index never decreases, and the bottom
  // index is never less than the top index at rest.  The smallest intermediate
  // value ever used is `bottom-1`, inside `take`.  Initializing `top` and
  // `bottom` at 1 suffices to prevent this computation from underflowing.
  atomic_init(&q->top, 1);
  atomic_init(&q->bottom, 1);
  Array* a = (Array*) malloc(sizeof(Array) + sizeof(Work*) * size_hint);
  atomic_init(&a->size, size_hint);
  atomic_init(&q->array, a);
}

void resize(Deque* q) {
  // This does not appear in https://fzn.fr/readings/ppopp13.pdf; I am imputing
  // it.
  printf("Resizing queue %p\n", q);
  Array *a = atomic_load_explicit(&q->array, memory_order_relaxed);
  size_t old_size = a->size;
  size_t new_size = old_size * 2;
  Array *new = malloc(sizeof(Array) + sizeof(Work*) * new_size);
  atomic_init(&new->size, new_size);
  size_t t = atomic_load_explicit(&q->top, memory_order_relaxed);
  size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
  for (size_t i = t; i < b; i++) {
    new->buffer[i % new_size] = a->buffer[i % old_size];
  }
  atomic_store_explicit(&q->array, new, memory_order_relaxed);
  // Question: When is it safe to free the old array *a?  In the original Chase
  // and Lev paper, that was taken care of by the garbage collector, which
  // presumably knew whether any other thread was currently in steal and trying
  // to read a value from it.
  // In our case, we can't safely free *a here, because another thread could
  // be trying to read it.  So we just leak the buffer -- since we only ever
  // grow these queues, and always by 2x, the leaked memory is never more than
  // the memory in use by the live queues.
}

Work* take(Deque *q) {
  size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed) - 1;
  Array *a = atomic_load_explicit(&q->array, memory_order_relaxed);
  atomic_store_explicit(&q->bottom, b, memory_order_relaxed);
  atomic_thread_fence(memory_order_seq_cst);
  size_t t = atomic_load_explicit(&q->top, memory_order_relaxed);
  Work* x;
  if (t <= b) {
    /* Non-empty queue. */
    x = atomic_load_explicit(&a->buffer[b % a->size], memory_order_relaxed);
    if (t == b) {
      /* Single last element in queue. */
      if (!atomic_compare_exchange_strong_explicit(
              &q->top, &t, t + 1, memory_order_seq_cst, memory_order_relaxed))
        /* Failed race. */
        x = EMPTY;
      atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
    }
  } else { /* Empty queue. */
    x = EMPTY;
    atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
  }
  return x;
}

void push(Deque *q, Work* w) {
  size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
  size_t t = atomic_load_explicit(&q->top, memory_order_acquire);
  Array *a = atomic_load_explicit(&q->array, memory_order_relaxed);
  if (b - t > a->size - 1) { /* Full queue. */
    resize(q);
    a = atomic_load_explicit(&q->array, memory_order_relaxed);
  }
  atomic_store_explicit(&a->buffer[b % a->size], w, memory_order_relaxed);
  atomic_thread_fence(memory_order_release);
  atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
}

Work* steal(Deque *q) {
  size_t t = atomic_load_explicit(&q->top, memory_order_acquire);
  atomic_thread_fence(memory_order_seq_cst);
  size_t b = atomic_load_explicit(&q->bottom, memory_order_acquire);
  Work* x = EMPTY;
  if (t < b) {
    /* Non-empty queue. */
    Array *a = atomic_load_explicit(&q->array, memory_order_consume);
    x = atomic_load_explicit(&a->buffer[t % a->size], memory_order_relaxed);
    if (!atomic_compare_exchange_strong_explicit(
            &q->top, &t, t + 1, memory_order_seq_cst, memory_order_relaxed))
      /* Failed race. */
      return ABORT;
  }
  return x;
}

/////////////////
// Worker loop //
/////////////////

int thread_count;

Deque* thread_queues;

atomic_bool done;

// Trampoline: Returns the next item to work on, or NULL if there aren't any.
Work* do_one_work(int id, Work* work) {
  printf("Worker %d running item %p\n", id, work);
  return (*(work->task))(id, work);
}

void do_work(int id, Work* work) {
  while (work != NULL) {
    work = do_one_work(id, work);
  }
}

// Trampoline: Returns the next item to work on, or NULL if there aren't any.
Work* join_work(Work* work) {
  int old_join_count = atomic_fetch_sub(&work->join_count, 1);
  if (old_join_count == 1) {
    return work;
  } else {
    return NULL;
  }
}

void* thread(void* payload) {
  int id = * (int*)payload;
  Deque* my_queue = &thread_queues[id];
  while (true) {
    Work* work = take(my_queue);
    if (work != EMPTY) {
      do_work(id, work);
    } else {
      // No work in my own queue
      Work* stolen = EMPTY;
      for (int i = 0; i < thread_count; ++i) {
        if (i == id) continue;
        stolen = steal(&thread_queues[i]);
        if (stolen == ABORT) {
          i--; continue; // Try again at the same i
        } else if (stolen == EMPTY) {
          continue;
        } else {
          // Found some work to do
          break;
        }
      }
      if (stolen == EMPTY) {
        // Even though the queues were all empty when I tried them, somebody
        // might have added some more work since.  Busy-wait until the global
        // "done" flag is set.
        if (atomic_load(&done)) {
          break;
        } else {
          continue;
        }
      } else {
        do_work(id, stolen);
      }
    }
  }
  printf("Worker %d finished\n", id);
  return NULL;
}

///////////////////////////
// Dex codegen interface //
///////////////////////////

// A (pointer to a) code-generated function.
// This should either return the result of calling `begin_pure_loop` or return `NULL`.
typedef Work* (*GenBlock)(int thread_id, void** env);

// A (pointer to a) code-generated function that is a loop body.
// This should either return the result of calling `begin_pure_loop` or return `NULL`.
typedef Work* (*GenLoopBody)(int thread_id, size_t iteration, void** env);

// Call this from Haskell once at the start of the process.
// The integer is the number of OS threads to spawn to run work-stealing.
void initialize_work_stealing(int nthreads);

// Call this from Haskell to run a top block with work-stealing.  When this
// exits, the work-stealing system is stopped, and results are written to their
// proper `Dest`s.
void execute_top_block(GenBlock body, void** env);

// Call this from code-gen at the end of each top-level block.
void finish_work_stealing();

// Call this from code-gen to start a loop that you want work-stealing to
// parallelize.
// This assumes that the environment frame for the loop body and for the
// continuation is the same.  That assumption isn't hard to change.
Work* begin_pure_loop(int thread_id, GenLoopBody body, GenBlock cont, void** env, size_t trip_count);

/////////////////////////
// Dex codegen support //
/////////////////////////

Work* run_gen_block_task(int thread_id, Work* self) {
  GenBlock body = (GenBlock)self->args[0];
  void** env = (void**)self->args[1];
  free(self);
  return body(thread_id, env);
}

Work* allocate_run_gen_block_work(int join_count, GenBlock cont, void** env) {
  Work* work = (Work*) malloc(sizeof(Work) + 2 * sizeof(int*));
  work->task = &run_gen_block_task;
  work->join_count = join_count;
  work->args[0] = cont;
  work->args[1] = env;
  return work;
}

// Return a `Work*` such that joining it `joiners` times is equivalent to joining
// the argument `cont` once.
// - `joiners` >= 1.
// - Do not use `cont` directly afterward, as this is allowed to mutate it.
Work* increase_cont_capacity(Work* cont, int joiners) {
  // One way to achieve the goal is to just atomically increase the `join_count`
  // of `cont` by `joiners - 1` and reuse it:
  atomic_fetch_add(&cont->join_count, joiners - 1);
  return cont;
  // An alternative would be allocate a new `Work` with `join_count` equal to
  // `joiners` and `task` to `join` the current `cont`.  The advantage of this
  // alternative is avoiding the atomic increment (on a potentially contentious
  // variable if `cont` has many joiners already); the disadvantage is the
  // allocation (which presumably entails some synchronization of its own), and
  // an extra indirection at the end due to executing that mini-task.
}

Work* execute_pure_loop_task(int id, Work* self);

Work* allocate_execute_pure_loop_work(
    Work* cont, GenLoopBody body, void** env,
    size_t start_iter, size_t end_iter) {
  Work* chunk = (Work*) malloc(sizeof(Work) + 5 * sizeof(int*));
  chunk->task = &execute_pure_loop_task;
  chunk->join_count = 0;
  chunk->args[0] = cont;
  chunk->args[1] = body;
  chunk->args[2] = env;
  chunk->args[3] = (void*)start_iter;
  chunk->args[4] = (void*)end_iter;
  return chunk;
}

// The recursive workhorse for running a pure loop.
Work* execute_pure_loop(
    int thread_id, Work* cont, GenLoopBody body, void** env,
    size_t start_iter, size_t end_iter) {
  int grain_size = 1;
  if (end_iter - start_iter <= grain_size) {
    // Few enough iterations; just do them.
    for (size_t i = start_iter; i < end_iter; i++) {
      do_work(thread_id, body(thread_id, i, env));
    }
    return join_work(cont);
  } else {
    // Break the loop up into chunks of iterations, and schedule those.
    int branching_factor = 2;
    div_t iters_per_branch = div(end_iter - start_iter, branching_factor);
    size_t this_iter = start_iter;
    // We are increasing the number of `Work`s that are permitted to join our
    // continuation `cont`.  Account for that.
    Work* subcont = increase_cont_capacity(cont, branching_factor);
    // Queue up all but one chunk of the loop for idle workers to potentially
    // steal.
    for (int i = 0; i < branching_factor - 1; i++) {
      size_t next_iter = this_iter + iters_per_branch.quot;
      if (i < iters_per_branch.rem) {
        // The chunks may be slightly uneven if the trip count is not evenly
        // divisible by the branching factor.
        next_iter++;
      }
      Work* chunk = allocate_execute_pure_loop_work(
          subcont, body, env, this_iter, next_iter);
      push(&thread_queues[thread_id], chunk);
      this_iter = next_iter;
    }
    // Do the last chunk immediately, to avoid allocating a `Work` for it.
    return execute_pure_loop(thread_id, subcont, body, env, this_iter, end_iter);
  }
}

Work* execute_pure_loop_task(int id, Work* self) {
  Work* cont = self->args[0];
  GenLoopBody body = self->args[1];
  void** env = self->args[2];
  size_t start_iter = (size_t)self->args[3];
  size_t end_iter = (size_t)self->args[4];
  return execute_pure_loop(id, cont, body, env, start_iter, end_iter);
}

Work* begin_pure_loop(int thread_id, GenLoopBody body, GenBlock cont, void** env, size_t trip_count) {
  // TODO: If the whole loop is smaller than the grain size for
  // execute_pure_loop, I can avoid allocating the `Work` for the continuation
  // too by just executing the iterations inline here.
  Work* k = allocate_run_gen_block_work(1, cont, env);
  return execute_pure_loop(thread_id, k, body, env, 0, trip_count);
}

pthread_t* the_threads;
int* tids;

void initialize_work_stealing(int nthreads) {
  // Check that top and bottom are 64-bit so they never overflow
  assert(sizeof(atomic_size_t) == 8);
  the_threads = (pthread_t*) malloc(nthreads * sizeof(pthread_t));
  tids = (int*) malloc(nthreads * sizeof(int));
  thread_queues = (Deque*) malloc(nthreads * sizeof(Deque));
  for (int i = 0; i < nthreads; ++i) {
    tids[i] = i;
    init(&thread_queues[i], 8);
  }
  thread_count = nthreads;
}

void execute_top_block(GenBlock body, void** env) {
  Work* job = allocate_run_gen_block_work(0, body, env);
  atomic_store(&done, false);
  push(&thread_queues[0], job);
  // TODO: Do we really want to start and kill all the threads for every top
  // level block, or is there a way to suspend and reuse them?
  for (int i = 0; i < thread_count; ++i) {
    if (pthread_create(&the_threads[i], NULL, thread, &tids[i]) != 0) {
      perror("failed to start the thread");
      exit(EXIT_FAILURE);
    }
  }
  for (int i = 0; i < thread_count; ++i) {
    if (pthread_join(the_threads[i], NULL) != 0) {
      perror("failed to join the thread");
      exit(EXIT_FAILURE);
    }
  }
  // We expect all the queues to be empty at this point.  TODO: Check?
}

void finish_work_stealing() {
  atomic_store(&done, true);
}

////////////////////
// Client program //
////////////////////

// A slightly silly program that iterates a single loop a synamic number of
// times, and has each loop iteration (and the coda) echo the trip count + 1,
// just to show that data can be mutated.

Work* gen_loop_body(int thread_id, size_t iteration, void** env) {
  int* payload = (int*)env[0];
  int item = *payload;
  printf("Loop iteration %d on worker %d, payload %d\n",
         iteration, thread_id, item);
  return NULL;
}

Work* end_gen_block(int thread_id, void** env) {
  int* payload = (int*)env[0];
  int item = *payload;
  printf("Finishing on worker %d, payload %d\n", thread_id, item);
  free(payload);
  free(env);
  finish_work_stealing();
  return NULL;
}

Work* start_gen_block(int thread_id, void** env) {
  int* payload = (int*)env[0];
  int item = *payload;
  printf("Starting on worker %d, payload %d\n", thread_id, item);
  *payload = item + 1;
  return begin_pure_loop(thread_id, gen_loop_body, end_gen_block, env, item);
}

int main(int argc, char **argv) {
  initialize_work_stealing(24);
  void** env = malloc(sizeof(int*));
  int* payload = malloc(sizeof(int));
  int num_iters = 200;
  *payload = num_iters;
  env[0] = payload;
  execute_top_block(&start_gen_block, env);
  int expected_output_lines =
      1    // "Starting"
      + 1  // "Finishing"
      + thread_count  // "Worker n finished"
      + 1  // Expected line report
      + num_iters  // Each loop iteration
      + 1  // "Worker running item" for the entry point
      + 1  // "Worker running item" for the end
      + (num_iters - 1)  // "Worker running item" for itermediates in the loop tree
      ;
  printf("Expect %d lines of output (including this one)\n",
         expected_output_lines);
  return 0;
}

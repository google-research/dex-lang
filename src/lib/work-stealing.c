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
typedef struct Work* (*Task)(struct Work*);

typedef struct Work {
  Task code;
  atomic_int join_count;
  void* args[];
} Work;

Work* EMPTY = -1;
Work* ABORT = -2;

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

void init(Deque* q, int size_hint) {
  // This does not appear in https://fzn.fr/readings/ppopp13.pdf; I am imputing
  // it.
  atomic_init(&q->top, 0);
  atomic_init(&q->bottom, 0);
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

#define nthreads 24

Deque* thread_queues;

atomic_bool done;

// Trampoline: Returns the next item to work on, or NULL if there aren't any.
Work* do_one_work(int id, Work* work) {
  printf("Worker %d running item %p\n", id, work);
  return (*(work->code))(work);
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
      for (int i = 0; i < nthreads; ++i) {
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
        // Even though the queues we all empty when I tried them, somebody
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

//////////////////////
// Dex loop support //
//////////////////////

// Return a `Work*` such that joining it `joiners` times is equivalent to joining
// the argument `cont` once.
// - `joiners` >= 1.
// - Do not use `cont` directly afterward, as this is allowed to mutate it.
Work* increase_cont_capacity(Work* cont, int joiners) {
  // One way to achieve the goal is to just atomically increase the `join_count`
  // of `cont` by `joiners - 1` and reuse it:
  atomic_add(&cont->join_count, joiners - 1);
  return cont;
  // An alternative would be allocate a new `Work` with `join_count` equal to
  // `joiners` and `task` to `join` the current `cont`.  The advantage of this
  // alternative is avoiding the atomic increment (on a potentially contentious
  // variable if `cont` has many joiners already); the disadvantage is the
  // allocation (which presumably entails some synchronization of its own), and
  // an extra indirection at the end due to executing that mini-task.
}

Work* execute_pure_loop(Work* cont, Task body, void* args[], int start_iter, int end_iter) {
  if (end_iter - start_iter <= 1) {
    // Few enough iterations; just do it.
    // TODO: Can we avoid allocating this Work struct that the body is going to just
    // immediately deallocate?  I guess the type of `body` would then have to change
    // from `Task`, and we'd have to code-gen it differently than if it were a `Task`.
    Work* work = (Work*) malloc(sizeof(Work) + 3 * sizeof(int*));
    work->code = body;
    work->join_count = 0;
    work->args[0] = args;
    work->args[1] = *start_iter;
    work->args[2] = cont;
    return body(work);
  } else {
    // Create Works that represent schedulable pieces of the loop.
    int branching_factor = 2;
    div_t iters_per_branch = div(end_iter - start_iter, branching_factor);
    int this_iter = start_iter;
    Work* subcont = increase_cont_capacity(cont, branching_factor);
    for (i = 0; i < branching_factor; i++) {
      int next_iter = this_iter + iters_per_branch.quot;
      if (i < iters_per_branch.rem) {
        next_iter++;
      }
      Work* section = (Work*) malloc(sizeof(Work) + 5 * sizeof(int*));
      section->code = &execute_pure_loop_task;
      section->join_count = 0;
      section->args[0] = subcont;
      section->args[1] = body;
      section->args[2] = args;
      section->args[3] = this_iter;
      section->args[4] = next_iter;
      // TODO I need to know my id so that I push onto my own queue
      int me = 0;
      if (i == branching_factor - 1) {
        // TODO Maybe I could skip allocating this Work, too?
        return do_one_work(me, section);
      } else {
        push(&thread_queues[me], section);
      }
      this_iter = next_iter;
    }  // This loop never completes because it hits the `return`
  }
}

Work* execute_pure_loop_task(Work* self) {
  Work* cont = self->args[0];
  Task body = self->args[1];
  void* args[] = self->args[2];
  int start_iter = self->args[3];  // Do I have to box these ints, or can I just store them?
  int end_iter = self->args[4];
  return execute_pure_loop(cont, body, args, start_iter, end_iter);
}

////////////////////
// Client program //
////////////////////

Work* print_task(Work* w) {
  int* payload = (int*)w->args[0];
  int item = *payload;
  printf("Did item %p with payload %d\n", w, item);
  Work* cont = (Work*)w->args[1];
  free(payload);
  free(w);
  return join_work(cont);
}

Work* done_task(Work* w) {
  free(w);
  atomic_store(&done, true);
  return NULL;
}

int main(int argc, char **argv) {
  // Check that top and bottom are 64-bit so they never overflow
  assert(sizeof(atomic_size_t) == 8);
  pthread_t threads[nthreads];
  int tids[nthreads];
  thread_queues = (Deque*) malloc(nthreads * sizeof(Deque));
  int nprints = 10;
  atomic_store(&done, false);
  Work* done_work = (Work*) malloc(sizeof(Work));
  done_work->code = &done_task;
  done_work->join_count = nthreads * nprints;
  for (int i = 0; i < nthreads; ++i) {
    tids[i] = i;
    init(&thread_queues[i], 8);
    for (int j = 0; j < nprints; ++j) {
      Work* work = (Work*) malloc(sizeof(Work) + 2 * sizeof(int*));
      work->code = &print_task;
      work->join_count = 0;
      int* payload = malloc(sizeof(int));
      *payload = 1000 * i + j;
      work->args[0] = payload;
      work->args[1] = done_work;
      push(&thread_queues[i], work);
    }
  }
  for (int i = 0; i < nthreads; ++i) {
    if (pthread_create(&threads[i], NULL, thread, &tids[i]) != 0) {
      perror("failed to start the thread");
      exit(EXIT_FAILURE);
    }
  }
  for (int i = 0; i < nthreads; ++i) {
    if (pthread_join(threads[i], NULL) != 0) {
      perror("failed to join the thread");
      exit(EXIT_FAILURE);
    }
  }
  printf("Expect %d lines of output (including this one)\n", 2 * nthreads * nprints + nthreads + 2);
  return 0;
}

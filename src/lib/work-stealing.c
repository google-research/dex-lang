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

typedef struct {
  // Question: Do we also want to tell the task the thread id of the worker
  // that's running it?  Maybe to support thread-local accumulators for
  // commutative reductions?
  // Oh yeah, also to know which worker's queue to put more stuff onto.
  void (*code)(void*);  // Always passed a pointer to the containing Work struct
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
  atomic_size_t top, bottom;
  _Atomic(Array *) array;
} Deque;

void init(Deque* q, int size_hint) {
  atomic_init(&q->top, 0);
  atomic_init(&q->bottom, 0);
  Array* a = (Array*) malloc(sizeof(Array) + sizeof(Work*) * size_hint);
  atomic_init(&a->size, size_hint);
  atomic_init(&q->array, a);
}

void resize(Deque* q) {
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

void do_work(int id, Work* work) {
  printf("Worker %d running item %p\n", id, work);
  (*(work->code))(work);
}

void* thread(void* payload) {
  int id = * (int*)payload;
  Deque* my_queue = &thread_queues[id];
  bool done = false;
  while (!done) {
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
        // Do I have a proof that all the queues are empty now, and the system
        // is therefore done, or are race conditions possible?
        done = true;
      } else {
        do_work(id, stolen);
      }
    }
  }
  printf("Worker %d finished\n", id);
  return NULL;
}

////////////////////
// Client program //
////////////////////

void print_task(Work* w) {
  int* payload = (int*)w->args[0];
  int item = *payload;
  printf("Did item %p with payload %d\n", w, item);
  free(payload);
  free(w);
}

int main(int argc, char **argv) {
  pthread_t threads[nthreads];
  int tids[nthreads];
  thread_queues = (Deque*) malloc(nthreads * sizeof(Deque));
  for (int i = 0; i < nthreads; ++i) {
    tids[i] = i;
    init(&thread_queues[i], 128);
    for (int j = 0; j < 100; ++j) {
      Work* work = (Work*) malloc(sizeof(Work) + sizeof(int*));
      work->code = (void (*) (void*))&print_task;
      work->join_count = 0;
      int* payload = malloc(sizeof(int));
      *payload = 1000 * i + j;
      work->args[0] = payload;
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
  return 0;
}

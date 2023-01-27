#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdatomic.h>
#include <stdbool.h>

int EMPTY = -1;
int ABORT = -2;

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
  void (*code)(void*);  // Always passed a pointer to the containing Work struct
  atomic_int join_count;
  void* args[];
} Work;

// Deque code adapted from https://fzn.fr/readings/ppopp13.pdf

typedef struct {
  atomic_size_t size;
  atomic_int buffer[];
} Array;

typedef struct {
  atomic_size_t top, bottom;
  _Atomic(Array *) array;
} Deque;

void init(Deque* q, int size_hint) {
  atomic_init(&q->top, 0);
  atomic_init(&q->bottom, 0);
  Array* a = (Array*) malloc(sizeof(Array) + sizeof(atomic_int) * size_hint);
  atomic_init(&a->size, size_hint);
  atomic_init(&q->array, a);
}

void resize(Deque* q) {
}

int take(Deque *q) {
  size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed) - 1;
  Array *a = atomic_load_explicit(&q->array, memory_order_relaxed);
  atomic_store_explicit(&q->bottom, b, memory_order_relaxed);
  atomic_thread_fence(memory_order_seq_cst);
  size_t t = atomic_load_explicit(&q->top, memory_order_relaxed);
  int x;
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

void push(Deque *q, int x) {
  size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
  size_t t = atomic_load_explicit(&q->top, memory_order_acquire);
  Array *a = atomic_load_explicit(&q->array, memory_order_relaxed);
  if (b - t > a->size - 1) { /* Full queue. */
    resize(q);
    a = atomic_load_explicit(&q->array, memory_order_relaxed);
  }
  atomic_store_explicit(&a->buffer[b % a->size], x, memory_order_relaxed);
  atomic_thread_fence(memory_order_release);
  atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
}

int steal(Deque *q) {
  size_t t = atomic_load_explicit(&q->top, memory_order_acquire);
  atomic_thread_fence(memory_order_seq_cst);
  size_t b = atomic_load_explicit(&q->bottom, memory_order_acquire);
  int x = EMPTY;
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

#define nthreads 24

Deque* thread_queues;

void do_work(int id, int work) {
  printf("Worker %d did item %d\n", id, work);
}

void* thread(void* payload) {
  int id = * (int*)payload;
  Deque* my_queue = &thread_queues[id];
  bool done = false;
  while (!done) {
    int work = take(my_queue);
    if (work != EMPTY) {
      do_work(id, work);
    } else {
      // No work in my own queue
      int stolen = EMPTY;
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
  printf("Finished %d\n", id);
  return NULL;
}

int main(int argc, char **argv) {
  pthread_t threads[nthreads];
  int tids[nthreads];
  thread_queues = (Deque*) malloc(nthreads * sizeof(Deque));
  for (int i = 0; i < nthreads; ++i) {
    tids[i] = i;
    init(&thread_queues[i], 128);
    for (int j = 0; j < 100; ++j) {
      push(&thread_queues[i], 1000 * i + j);
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

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@

predicate arraylist(struct arraylist *a; int size, int capacity) =
  a->data |-> ?data &*& a->size |-> size &*& a->capacity |-> capacity &*&
  malloc_block_arraylist(a) &*&
  data != 0 &*&
  ints_range(size, 0, capacity) &*&
  capacity > 0 &*&
  malloc_block_pointers(data, capacity) &*&
  pointers(data, capacity, _);

@*/

struct arraylist *create_arraylist() 
//@ requires true;
//@ ensures arraylist(result, 0, 100);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  //@ close arraylist(a, 0, 100);
  return a; 
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a, ?size, ?capacity) &*& ints_range(i, 0, size);
//@ ensures arraylist(a, size, capacity);
{
  //@ open arraylist(a, size, capacity);
  void *r = a->data[i];
  //@ close arraylist(a, size, capacity);
  return r;
}

int list_length(struct arraylist *a)
//@ requires arraylist(a, ?size, ?capacity);
//@ ensures arraylist(a, size, capacity) &*& result == size;
{
  //@ open arraylist(a, size, capacity);
  int r = a->size;
  //@ close arraylist(a, size, capacity);
  return r;
}

void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?size, ?capacity) &*& ints_range(size, 0, INT_MAX - 1);
//@ ensures arraylist(a, size + 1, ?newCapacity);
{
  //@ open arraylist(a, size, capacity);
  int size0 = 0;
  void** data0 = 0;
  if(a->capacity <= a->size) {
    data0 = a->data;
    size0 = a->size;
    int capacity0 = a->capacity;

    if (SIZE_MAX / sizeof(void *) < (size_t)capacity0 * 2 + 1) abort();

    void** newData = malloc(((size_t)capacity0 * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();

    //@ assert malloc_block_pointers(data0, capacity0);
    //@ assert pointers(data0, capacity0, ?oldvs);
    memcpy(newData, data0, (size_t)size0 * sizeof(void*));
    //@ assert pointers(newData, capacity0, oldvs);
    //@ pointers_split(newData, size0);
    //@ pointers_split(data0, size0);

    a->data = newData;

    if (INT_MAX / 2 - 1 < capacity0) abort();
    a->capacity = capacity0 * 2 + 1;

    //@ pointers_join(data0);
    free(data0);

    //@ pointers_join(newData);
  }
  size0 = a->size;
  data0 = a->data;
  //@ assert pointers(data0, ?cap2, ?vs2);
  //@ pointers_split(data0, size0);
  data0[size0] = v;
  //@ pointers_join(data0);
  a->size += 1;

  //@ close arraylist(a, size0 + 1, a->capacity);
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a, ?size, ?capacity) &*& ints_range(n, 0, size) &*& size > 0;
//@ ensures arraylist(a, size - 1, capacity);
{
  //@ open arraylist(a, size, capacity);
  void** data = a->data;
  int size0 = a->size;

  //@ assert pointers(data, capacity, ?vs);
  //@ pointers_split(data, n);
  //@ pointers_split(data + n, size0 - n);
  //@ pointers_split(data + n + 1, size0 - n - 1);

  memmove(data + n, data + n + 1, (unsigned int) (size0 - n - 1) * sizeof(void *));

  //@ pointers_join(data + n);
  //@ pointers_join(data);

  a->size = a->size - 1;

  //@ close arraylist(a, size0 - 1, capacity);
}

void list_dispose(struct arraylist* a)
//@ requires arraylist(a, ?size, ?capacity);
//@ ensures true;
{
  //@ open arraylist(a, size, capacity);
  void** data = a->data;
  int size0 = a->size;
  int capacity0 = a->capacity;
  //@ open pointers(data, capacity0, _);
  free(data);
  free(a);
}

int main()
//@ requires true;
//@ ensures true;
{
  struct arraylist* a = create_arraylist();
  void* tmp = 0;
  list_add(a, (void *)10);
  list_add(a, (void *)20);

  tmp = list_get(a, 1);
  assert(tmp == (void*) 20);
  list_dispose(a);

  return 0;
}
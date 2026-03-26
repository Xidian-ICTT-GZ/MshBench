#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

struct arraylist
{
  void **data;
  int size;
  int capacity;
};

/*@

predicate arraylist(struct arraylist *a; int size, int capacity) =
  a != 0 &*&
  a->data |-> ?data &*&
  a->size |-> size &*&
  a->capacity |-> capacity &*&
  capacity >= 0 &*& size >= 0 &*& size <= capacity &*&
  malloc_block_arraylist(a) &*&
  data != 0 &*&
  malloc_block_pointers(data, capacity) &*&
  pointers(data, capacity, ?vs);

@*/

struct arraylist *create_arraylist()

//@ requires true;
//@ ensures arraylist(result, 0, 100);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if (a == 0)
    abort();
  a->size = 0;
  data = malloc(100 * sizeof(void *));
  if (data == 0)
    abort();
  a->data = data;
  a->capacity = 100;
  //@ close pointers((void**)data, 100, _);
  //@ close arraylist(a, 0, 100);
  return a;
}

void *list_get(struct arraylist *a, int i)

//@ requires arraylist(a, ?size, ?cap) &*& 0 <= i &*& i < size;
//@ ensures arraylist(a, size, cap);
{
  //@ open arraylist(a, size, cap);
  //@ assert a->data |-> ?data;
  //@ open pointers(data, cap, ?vs);
  //@ assert pointers(data, cap, vs);
  //@ close pointers(data, cap, vs);
  //@ close arraylist(a, size, cap);
  return a->data[i];
}

int list_length(struct arraylist *a)

//@ requires arraylist(a, ?size, ?cap);
//@ ensures arraylist(a, size, cap) &*& result == size;
{
  //@ open arraylist(a, size, cap);
  //@ close arraylist(a, size, cap);
  return a->size;
}

void list_add(struct arraylist *a, void *v)

//@ requires arraylist(a, ?size, ?cap);
//@ ensures arraylist(a, size + 1, ?cap2);
{
  //@ open arraylist(a, size, cap);
  int size = 0;
  void **data = 0;
  if (a->capacity <= a->size)
  {
    data = a->data;
    size = a->size;
    int capacity = a->capacity;

    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1)
      abort();

    void **newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void *));
    if (newData == 0)
      abort();

    //@ open pointers(data, capacity, ?vsOld);
    memcpy(newData, data, (size_t)size * sizeof(void *));

    a->data = newData;

    if (INT_MAX / 2 - 1 < capacity)
      abort();
    a->capacity = capacity * 2 + 1;

    //@ close pointers((void**)newData, capacity * 2 + 1, _);
    //@ close pointers(data, capacity, vsOld);
    free(data);
    //@ open pointers(data, capacity, vsOld);
  }
  size = a->size;
  data = a->data;
  //@ assert a->capacity |-> ?capNow;
  //@ open pointers(data, capNow, ?vsNow);
  data[size] = v;
  //@ close pointers(data, capNow, vsNow);
  a->size += 1;
  //@ close arraylist(a, size + 1, capNow);
}

void list_remove_nth(struct arraylist *a, int n)

//@ requires arraylist(a, ?size, ?cap) &*& 0 <= n &*& n < size;
//@ ensures arraylist(a, size - 1, cap);
{
  //@ open arraylist(a, size, cap);
  void **data = a->data;
  int size = a->size;

  //@ open pointers(data, cap, ?vs);
  memmove(data + n, data + n + 1, (unsigned int)(size - n - 1) * sizeof(void *));
  //@ close pointers(data, cap, vs);

  a->size = a->size - 1;
  //@ close arraylist(a, size - 1, cap);
}

void list_dispose(struct arraylist *a)

//@ requires arraylist(a, ?size, ?cap);
//@ ensures true;
{
  //@ open arraylist(a, size, cap);
  void **data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  //@ open pointers(data, cap, ?vs);
  free(data);
  free(a);
}

int main()

//@ requires true;
//@ ensures true;
{
  struct arraylist *a = create_arraylist();
  void *tmp = 0;
  list_add(a, (void *)10);
  list_add(a, (void *)20);

  tmp = list_get(a, 1);
  assert(tmp == (void *)20);
  list_dispose(a);

  return 0;
}
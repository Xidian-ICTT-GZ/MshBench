#include <stdint.h>
#include <stdlib.h>
#include <string.h>
struct arraylist
{
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a, int size, int capacity) =
  a->data |-> ?data &*& a->size |-> size &*& a->capacity |-> capacity &*&
  malloc_block_arraylist(a) &*&
  data != 0 &*& malloc_block(data, capacity * sizeof(void*)) &*&
  chars((void*)data, capacity * sizeof(void*), _) &*&
  size >= 0 &*& size <= capacity &*& capacity > 0 &*& capacity <= INT_MAX;
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
  return a;
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a, ?size, ?capacity) &*& i >= 0 &*& i < size;
//@ ensures arraylist(a, size, capacity);
{
  //@ open arraylist(a, size, capacity);
  //@ chars_split((void*)(a->data), i * sizeof(void*));
  //@ chars_split((void*)(a->data + i), sizeof(void*));
  void *result = a->data[i];
  //@ chars_join((void*)(a->data + i));
  //@ chars_join((void*)(a->data));
  //@ close arraylist(a, size, capacity);
  return result;
}

int list_length(struct arraylist *a)
//@ requires arraylist(a, ?size, ?capacity);
//@ ensures arraylist(a, size, capacity) &*& result == size;
{
  //@ open arraylist(a, size, capacity);
  int result = a->size;
  //@ close arraylist(a, size, capacity);
  return result;
}

void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?size, ?capacity) &*& size < INT_MAX;
//@ ensures arraylist(a, size + 1, _);
{
  int size = 0;
  void **data = 0;
  //@ open arraylist(a, size, capacity);
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

    memcpy(newData, data, (size_t)size * sizeof(void *));
    //@ chars_split((void*)newData, size * sizeof(void*));

    a->data = newData;

    if (INT_MAX / 2 - 1 < capacity)
      abort();
    a->capacity = capacity * 2 + 1;

    free(data);
    //@ close arraylist(a, size, capacity * 2 + 1);
  } else {
    //@ close arraylist(a, size, capacity);
  }
  //@ open arraylist(a, _, ?cap);
  size = a->size;
  data = a->data;
  //@ chars_split((void*)data, size * sizeof(void*));
  //@ chars_split((void*)(data + size), sizeof(void*));
  data[size] = v;
  //@ chars_join((void*)(data + size));
  //@ chars_join((void*)data);
  a->size += 1;
  //@ close arraylist(a, size + 1, cap);
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a, ?size, ?capacity) &*& n >= 0 &*& n < size - 1;
//@ ensures arraylist(a, size - 1, capacity);
{
  //@ open arraylist(a, size, capacity);
  void **data = a->data;
  int size = a->size;

  memmove(data + n, data + n + 1, (unsigned int)(size - n - 1) * sizeof(void *));

  a->size = a->size - 1;
  //@ close arraylist(a, size - 1, capacity);
}

void list_dispose(struct arraylist *a)
//@ requires arraylist(a, ?size, ?capacity);
//@ ensures true;
{
  //@ open arraylist(a, size, capacity);
  void **data = a->data;
  int size = a->size;
  int capacity = a->capacity;
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
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist
{
  void **data;
  int size;
  int capacity;
};

/*@ predicate arraylist(struct arraylist *a; int sz, int cap) =
  a->size |-> sz &*& a->capacity |-> cap &*& a->data |-> ?data &*&
  malloc_block(data, (size_t)cap * sizeof(void *)) &*&
  sz >= 0 &*& cap > 0 &*& sz <= cap;
@*/

struct arraylist *create_arraylist()
//@ requires true;
//@ ensures arraylist(result, 0, 100) &*& malloc_block(result, sizeof(struct arraylist));
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
//@ requires arraylist(a, ?sz, ?cap) &*& 0 <= i &*& i < sz;
//@ ensures arraylist(a, sz, cap);
{
  return a->data[i];
}

int list_length(struct arraylist *a)
//@ requires arraylist(a, ?sz, ?cap);
//@ ensures arraylist(a, sz, cap) &*& result == sz;
{
  return a->size;
}

void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?sz, ?cap) &*& sz < INT_MAX &*& cap > 0;
//@ ensures arraylist(a, sz + 1, ?newcap) &*& newcap >= sz + 1;
{
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

    memcpy(newData, data, (size_t)size * sizeof(void *));

    a->data = newData;

    if (INT_MAX / 2 - 1 < capacity)
      abort();
    a->capacity = capacity * 2 + 1;

    free(data);
  }
  size = a->size;
  data = a->data;
  data[size] = v;
  a->size += 1;
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a, ?sz, ?cap) &*& 0 <= n &*& n < sz;
//@ ensures arraylist(a, sz - 1, cap);
{
  void **data = a->data;
  int size = a->size;

  memmove(data + n, data + n + 1, (unsigned int)(size - n - 1) * sizeof(void *));

  a->size = a->size - 1;
}

void list_dispose(struct arraylist *a)
//@ requires arraylist(a, ?sz, ?cap) &*& malloc_block(a, sizeof(struct arraylist));
//@ ensures true;
{
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
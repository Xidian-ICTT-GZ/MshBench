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
predicate pointers(void **data, int count;) =
  count <= 0 ? emp : pointer(data, _) &*& pointers(data + 1, count - 1);

predicate arraylist(struct arraylist *a; int sz, int cap) =
  malloc_block_arraylist(a) &*&
  a->size |-> sz &*& a->capacity |-> cap &*& a->data |-> ?data &*&
  malloc_block(data, (size_t)cap * sizeof(void *)) &*&
  pointers(data, cap) &*&
  sz >= 0 &*& cap > 0 &*& sz <= cap;
@*/

/*@
lemma void pointers_split(void **data, int i)
  requires pointers(data, ?n) &*& 0 <= i &*& i <= n;
  ensures pointers(data, i) &*& pointers(data + i, n - i);
{
  if (i == 0) {
  } else {
    open pointers(data, n);
    pointers_split(data + 1, i - 1);
    close pointers(data, i);
  }
}

lemma void pointers_merge(void **data, int i)
  requires pointers(data, i) &*& pointers(data + i, ?j);
  ensures pointers(data, i + j);
{
  if (i == 0) {
    open pointers(data, 0);
  } else {
    open pointers(data, i);
    pointers_merge(data + 1, i - 1);
    close pointers(data, i + j);
  }
}
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
  //@ chars_to_pointers(data, 100);
  //@ close pointers((void **)data, 100);
  //@ close arraylist(a, 0, 100);
  return a;
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a, ?sz, ?cap) &*& 0 <= i &*& i < sz;
//@ ensures arraylist(a, sz, cap);
{
  //@ open arraylist(a, sz, cap);
  void **data = a->data;
  //@ pointers_split(data, i);
  //@ open pointers(data + i, cap - i);
  void *result = data[i];
  //@ close pointers(data + i, cap - i);
  //@ pointers_merge(data, i);
  //@ close arraylist(a, sz, cap);
  return result;
}

int list_length(struct arraylist *a)
//@ requires arraylist(a, ?sz, ?cap);
//@ ensures arraylist(a, sz, cap) &*& result == sz;
{
  //@ open arraylist(a, sz, cap);
  int result = a->size;
  //@ close arraylist(a, sz, cap);
  return result;
}

void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?sz, ?cap) &*& sz < INT_MAX;
//@ ensures arraylist(a, sz + 1, _);
{
  //@ open arraylist(a, sz, cap);
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

    //@ pointers_to_chars(data, capacity);
    //@ chars_to_pointers(newData, capacity * 2 + 1);
    //@ close pointers(newData, capacity * 2 + 1);
    memcpy(newData, data, (size_t)size * sizeof(void *));

    a->data = newData;

    if (INT_MAX / 2 - 1 < capacity)
      abort();
    a->capacity = capacity * 2 + 1;

    free(data);
  }
  size = a->size;
  data = a->data;
  //@ int newcap = a->capacity;
  //@ pointers_split(data, size);
  //@ open pointers(data + size, newcap - size);
  data[size] = v;
  //@ close pointers(data + size, newcap - size);
  //@ pointers_merge(data, size);
  a->size = size + 1;
  //@ close arraylist(a, size + 1, newcap);
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a, ?sz, ?cap) &*& 0 <= n &*& n < sz;
//@ ensures arraylist(a, sz - 1, cap);
{
  //@ open arraylist(a, sz, cap);
  void **data = a->data;
  int size = a->size;

  //@ pointers_to_chars(data, cap);
  memmove(data + n, data + n + 1, (unsigned int)(size - n - 1) * sizeof(void *));
  //@ chars_to_pointers(data, cap);
  //@ close pointers(data, cap);

  a->size = a->size - 1;
  //@ close arraylist(a, sz - 1, cap);
}

void list_dispose(struct arraylist *a)
//@ requires arraylist(a, ?sz, ?cap);
//@ ensures true;
{
  //@ open arraylist(a, sz, cap);
  void **data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  //@ pointers_to_chars(data, cap);
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
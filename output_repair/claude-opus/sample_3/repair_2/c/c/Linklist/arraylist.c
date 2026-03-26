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
predicate ptrs(void **data, int count;) =
  count <= 0 ? emp : pointer(data, _) &*& ptrs(data + 1, count - 1);

predicate arraylist(struct arraylist *a; int sz, int cap) =
  malloc_block_arraylist(a) &*&
  a->size |-> sz &*& a->capacity |-> cap &*& a->data |-> ?data &*&
  malloc_block_pointers(data, cap) &*&
  ptrs(data, cap) &*&
  sz >= 0 &*& cap > 0 &*& sz <= cap;
@*/

/*@
lemma void ptrs_split(void **data, int i)
  requires ptrs(data, ?n) &*& 0 <= i &*& i <= n;
  ensures ptrs(data, i) &*& ptrs(data + i, n - i);
{
  if (i == 0) {
  } else {
    open ptrs(data, n);
    ptrs_split(data + 1, i - 1);
    close ptrs(data, i);
  }
}

lemma void ptrs_merge(void **data, int i)
  requires ptrs(data, i) &*& ptrs(data + i, ?j);
  ensures ptrs(data, i + j);
{
  if (i == 0) {
    open ptrs(data, 0);
  } else {
    open ptrs(data, i);
    ptrs_merge(data + 1, i - 1);
    close ptrs(data, i + j);
  }
}

lemma void ptrs_to_chars(void **data, int count)
  requires ptrs(data, count) &*& count >= 0;
  ensures chars((char *)data, count * sizeof(void *), _);
{
  if (count == 0) {
    open ptrs(data, 0);
    close chars((char *)data, 0, nil);
  } else {
    open ptrs(data, count);
    ptrs_to_chars(data + 1, count - 1);
    pointer_to_chars(data);
    chars_join((char *)data);
  }
}

lemma void chars_to_ptrs(void **data, int count)
  requires chars((char *)data, count * sizeof(void *), _) &*& count >= 0;
  ensures ptrs(data, count);
{
  if (count == 0) {
    chars_to_chars(data, 0);
    open chars((char *)data, 0, _);
    close ptrs(data, 0);
  } else {
    chars_split((char *)data, sizeof(void *));
    chars_to_pointer(data);
    chars_to_ptrs(data + 1, count - 1);
    close ptrs(data, count);
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
  //@ chars_to_ptrs(data, 100);
  //@ close arraylist(a, 0, 100);
  return a;
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a, ?sz, ?cap) &*& 0 <= i &*& i < sz;
//@ ensures arraylist(a, sz, cap);
{
  //@ open arraylist(a, sz, cap);
  void **data = a->data;
  //@ ptrs_split(data, i);
  //@ open ptrs(data + i, cap - i);
  void *result = data[i];
  //@ close ptrs(data + i, cap - i);
  //@ ptrs_merge(data, i);
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

    //@ ptrs_to_chars(data, capacity);
    //@ chars_to_ptrs(newData, capacity * 2 + 1);
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
  //@ ptrs_split(data, size);
  //@ open ptrs(data + size, newcap - size);
  data[size] = v;
  //@ close ptrs(data + size, newcap - size);
  //@ ptrs_merge(data, size);
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

  //@ ptrs_to_chars(data, cap);
  memmove(data + n, data + n + 1, (unsigned int)(size - n - 1) * sizeof(void *));
  //@ chars_to_ptrs(data, cap);

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
  //@ ptrs_to_chars(data, cap);
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
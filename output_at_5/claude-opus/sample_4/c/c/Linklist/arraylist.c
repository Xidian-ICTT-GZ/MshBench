#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/*@
predicate arraylist_pred(struct arraylist *a; void **data, int size, int capacity) =
  a->data |-> data &*& a->size |-> size &*& a->capacity |-> capacity &*&
  malloc_block_array(void*, data, capacity) &*& malloc_block(a);
@*/

struct arraylist {
  void **data;
  int size;
  int capacity;
};

struct arraylist *create_arraylist()
//@ requires true;
//@ ensures arraylist_pred(result, ?data, 0, 100);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  if(a == 0) abort();
  void *data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->size = 0;
  a->data = data;
  a->capacity = 100;
  //@ close arraylist_pred(a, a->data, 0, 100);
  return a; 
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist_pred(a, ?data, ?size, ?capacity) &*& 0 <= i &*& i < size;
//@ ensures arraylist_pred(a, data, size, capacity) &*& result == data[i];
{
  //@ open arraylist_pred(a, data, size, capacity);
  void *res = a->data[i];
  //@ close arraylist_pred(a, data, size, capacity);
  return res;
}

int list_length(struct arraylist *a)
//@ requires arraylist_pred(a, ?data, ?size, ?capacity);
//@ ensures arraylist_pred(a, data, size, capacity) &*& result == size;
{
  //@ open arraylist_pred(a, data, size, capacity);
  int res = a->size;
  //@ close arraylist_pred(a, data, size, capacity);
  return res;
}

void list_add(struct arraylist *a, void *v)
//@ requires arraylist_pred(a, ?data, ?size, ?capacity);
//@ ensures arraylist_pred(a, a->data, size + 1, a->capacity);
{
  //@ open arraylist_pred(a, data, size, capacity);
  if(a->capacity <= a->size) {
    void** oldData = data;
    int oldSize = size;
    int oldCapacity = capacity;
    if (SIZE_MAX / sizeof(void *) < (size_t)oldCapacity * 2 + 1) abort();
    void** newData = malloc(((size_t)oldCapacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    memcpy(newData, oldData, (size_t)oldSize * sizeof(void*));
    a->data = newData;
    if (INT_MAX / 2 - 1 < oldCapacity) abort();
    a->capacity = oldCapacity * 2 + 1;
    free(oldData);
    data = newData; capacity = a->capacity;
  }
  data = a->data;
  size = a->size;
  data[size] = v;
  a->size = size + 1;
  //@ close arraylist_pred(a, a->data, size + 1, a->capacity);
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist_pred(a, ?data, ?size, ?capacity) &*& 0 <= n &*& n < size;
//@ ensures arraylist_pred(a, data, size - 1, capacity);
{
  //@ open arraylist_pred(a, data, size, capacity);
  void** data0 = a->data;
  int size0 = a->size;
  memmove(data0 + n, data0 + n + 1, (unsigned int)(size0 - n - 1) * sizeof(void *));
  a->size = size0 - 1;
  //@ close arraylist_pred(a, data0, size0 - 1, capacity);
}

void list_dispose(struct arraylist* a)
//@ requires arraylist_pred(a, ?data, ?size, ?capacity);
//@ ensures true;
{
  //@ open arraylist_pred(a, data, size, capacity);
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
  //@ assert tmp == (void*)20;
  list_dispose(a);
  return 0;
}
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"
//@ #include "malloc.gh"
//@ #include "memcpy.gh"
//@ #include "memmove.gh"

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a; void **data, int size, int capacity) =
  a != 0 &*&
  a->data |-> data &*& a->size |-> size &*& a->capacity |-> capacity &*&
  malloc_block_arraylist(a) &*&
  data != 0 &*& malloc_block(data, (size_t)capacity * sizeof(void*)) &*&
  0 <= size &*& size <= capacity;
@*/

struct arraylist *create_arraylist() 
//@ requires true;
//@ ensures arraylist(result, ?data, 0, 100);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  //@ close arraylist(a, (void**)data, 0, 100);
  return a; 
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a, ?data, ?size, ?capacity) &*& 0 <= i &*& i < size;
//@ ensures arraylist(a, data, size, capacity);
{
  //@ open arraylist(a, data, size, capacity);
  void* result = a->data[i];
  //@ close arraylist(a, data, size, capacity);
  return result;
}

int list_length(struct arraylist *a)
//@ requires arraylist(a, ?data, ?size, ?capacity);
//@ ensures arraylist(a, data, size, capacity) &*& result == size;
{
  //@ open arraylist(a, data, size, capacity);
  int r = a->size;
  //@ close arraylist(a, data, size, capacity);
  return r;
}

void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?data, ?size, ?capacity);
//@ ensures arraylist(a, ?data2, size + 1, ?capacity2) &*& size + 1 <= capacity2;
{
  //@ open arraylist(a, data, size, capacity);
  int size0 = 0;
  void** data0 = 0;
  if(a->capacity <= a->size) {
    data0 = a->data;
    size0 = a->size;
    int capacity0 = a->capacity;
    
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity0 * 2 + 1) abort();
    
    
    
    void** newData = malloc(((size_t)capacity0 * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    
    
    memcpy(newData, data0, (size_t)size0 * sizeof(void*));
    
    a->data = newData;
    
    if (INT_MAX / 2 - 1 < capacity0) abort();
    a->capacity = capacity0 * 2 + 1;
    
    free(data0);
  }
  size0 = a->size;
  data0 = a->data;
  data0[size0] = v;
  a->size += 1;
  //@ close arraylist(a, a->data, size + 1, a->capacity);
  
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a, ?data, ?size, ?capacity) &*& 0 <= n &*& n < size;
//@ ensures arraylist(a, data, size - 1, capacity);
{
  //@ open arraylist(a, data, size, capacity);
  void** data0 = a->data;
  int size0 = a->size;
  
  
  
  
  
  memmove(data0 + n, data0 + n + 1, (unsigned int) (size0 - n - 1) * sizeof(void *));
  
  a->size = a->size - 1;
  
  //@ close arraylist(a, data0, size - 1, capacity);
  
}

void list_dispose(struct arraylist* a)
//@ requires arraylist(a, ?data, ?size, ?capacity);
//@ ensures true;
{
  //@ open arraylist(a, data, size, capacity);
  void** data0 = a->data;
  int size0 = a->size;
  int capacity0 = a->capacity;
  free(data0);
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
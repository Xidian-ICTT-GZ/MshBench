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
predicate arraylist(struct arraylist *a; void **data, int size, int capacity) =
  a != 0 &*&
  a->data |-> data &*&
  a->size |-> size &*&
  a->capacity |-> capacity &*&
  0 <= size &*& size <= capacity &*&
  data != 0 &*&
  malloc_block_arraylist(a) &*&
  pointers(data, capacity, _);
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
  //@ close pointers((void**)data, 100, _);
  //@ close arraylist(a, (void**)data, 0, 100);
  return a; 
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a, ?data, ?size, ?cap) &*& 0 <= i &*& i < size;
//@ ensures arraylist(a, data, size, cap);
{
  //@ open arraylist(a, data, size, cap);
  void *res = a->data[i];
  //@ close arraylist(a, data, size, cap);
  return res;
}

int list_length(struct arraylist *a)
//@ requires arraylist(a, ?data, ?size, ?cap);
//@ ensures arraylist(a, data, size, cap) &*& result == size;
{
  //@ open arraylist(a, data, size, cap);
  int res = a->size;
  //@ close arraylist(a, data, size, cap);
  return res;
}

void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?data, ?size, ?cap);
//@ ensures arraylist(a, ?data2, size + 1, ?cap2);
{
  //@ open arraylist(a, data, size, cap);
  int size = 0;
  void** data = 0;
  if(a->capacity <= a->size) {
    data = a->data;
    size = a->size;
    int capacity = a->capacity;
    
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    
    
    
    //@ open pointers(data, capacity, _);
    void** newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    //@ close pointers(newData, (size_t)capacity * 2 + 1, _);
    
    
    //@ open pointers(newData, (size_t)capacity * 2 + 1, _);
    memcpy(newData, data, (size_t)size * sizeof(void*));
    //@ close pointers(newData, (size_t)capacity * 2 + 1, _);
    
    a->data = newData;
    
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    
    free(data);
  }
  size = a->size;
  data = a->data;
  //@ open pointers(data, a->capacity, _);
  data[size] = v;
  //@ close pointers(data, a->capacity, _);
  a->size += 1;
  //@ close arraylist(a, a->data, size + 1, a->capacity);
  
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a, ?data, ?size, ?cap) &*& 0 <= n &*& n < size;
//@ ensures arraylist(a, data, size - 1, cap);
{
  //@ open arraylist(a, data, size, cap);
  void** data = a->data;
  int size = a->size;
  
  
  
  
  
  //@ open pointers(data, cap, _);
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  //@ close pointers(data, cap, _);
  
  a->size = a->size - 1;
  //@ close arraylist(a, data, size - 1, cap);
  
}

void list_dispose(struct arraylist* a)
//@ requires arraylist(a, ?data, ?size, ?cap);
//@ ensures true;
{
  //@ open arraylist(a, data, size, cap);
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  //@ open pointers(data, capacity, _);
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
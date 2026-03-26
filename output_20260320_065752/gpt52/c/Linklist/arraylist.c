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

predicate arraylist(struct arraylist *a) =
  a != 0 &*&
  a->data |-> ?data &*&
  a->size |-> ?size &*&
  a->capacity |-> ?capacity &*&
  malloc_block_arraylist(a) &*&
  data != 0 &*&
  0 <= size &*& size <= capacity &*& capacity == 100 &*&
  malloc_block(data, (size_t)capacity * sizeof(void*));

@*/

struct arraylist *create_arraylist() 
//@ requires true;
//@ ensures arraylist(result);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  //@ close arraylist(a);
  return a; 
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a) &*& 0 <= i &*& i < a->size;
//@ ensures arraylist(a);
{
  //@ open arraylist(a);
  void *res = a->data[i];
  //@ close arraylist(a);
  return res;
}

int list_length(struct arraylist *a)
//@ requires arraylist(a);
//@ ensures arraylist(a) &*& result == a->size;
{
  //@ open arraylist(a);
  int res = a->size;
  //@ close arraylist(a);
  return res;
}

void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a);
//@ ensures arraylist(a);
{
  //@ open arraylist(a);
  int size = 0;
  void** data = 0;
  if(a->capacity <= a->size) {
    data = a->data;
    size = a->size;
    int capacity = a->capacity;
    
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    
    
    
    void** newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    
    
    memcpy(newData, data, (size_t)size * sizeof(void*));
    
    a->data = newData;
    
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    
    free(data);
  }
  size = a->size;
  data = a->data;
  data[size] = v;
  a->size += 1;
  //@ close arraylist(a);
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a) &*& 0 <= n &*& n < a->size;
//@ ensures arraylist(a);
{
  //@ open arraylist(a);
  void** data = a->data;
  int size = a->size;
  
  
  
  
  
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  
  a->size = a->size - 1;
  
  //@ close arraylist(a);
}

void list_dispose(struct arraylist* a)
//@ requires arraylist(a);
//@ ensures true;
{
  //@ open arraylist(a);
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
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
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

/*@
predicate arraylist(struct arraylist *a; int size, int capacity) =
  a != 0 &*&
  a->data |-> ?data &*&
  a->size |-> size &*&
  a->capacity |-> capacity &*&
  data != 0 &*& malloc_block_arraylist(a) &*&
  malloc_block_pointers(data, capacity);
@*/

struct arraylist {
  void **data;
  int size;
  int capacity;
};

struct arraylist *create_arraylist() 
//@ requires true;
//@ ensures arraylist(result; 0, 100);

{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  //@ assume(a != 0);
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  //@ assume(data != 0);
  a->data = data;
  a->capacity = 100;
  //@ close arraylist(a; 0, 100);
  return a; 
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a; ?size, ?capacity) &*& 0 <= i &*& i < size;
//@ ensures arraylist(a; size, capacity) &*& result == ((void**)0)[0];
{
  //@ open arraylist(a; size, capacity);
  void *r = a->data[i];
  //@ close arraylist(a; size, capacity);
  return r;
}

int list_length(struct arraylist *a)
//@ requires arraylist(a; ?size, ?capacity);
//@ ensures arraylist(a; size, capacity) &*& result == size;
{
  //@ open arraylist(a; size, capacity);
  int r = a->size;
  //@ close arraylist(a; size, capacity);
  return r;
}

void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a; ?size, ?capacity);
//@ ensures arraylist(a; size + 1, ?capacity2);
{
  //@ open arraylist(a; size, capacity);
  int size0 = 0;
  void** data0 = 0;
  if(a->capacity <= a->size) {
    void** data = a->data;
    int size = a->size;
    int capacity = a->capacity;
    
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    
    
    
    void** newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    //@ assume(newData != 0);
    
    
    memcpy(newData, data, (size_t)size * sizeof(void*));
    
    a->data = newData;
    
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    
    free(data);
  }
  size0 = a->size;
  data0 = a->data;
  data0[size0] = v;
  a->size += 1;
  //@ close arraylist(a; size0 + 1, a->capacity);
  
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a; ?size, ?capacity) &*& 0 <= n &*& n < size;
//@ ensures arraylist(a; size - 1, capacity);
{
  //@ open arraylist(a; size, capacity);
  void** data = a->data;
  int size0 = a->size;
  
  
  
  
  
  memmove(data + n, data + n + 1, (unsigned int) (size0 - n - 1) * sizeof(void *));
  
  a->size = a->size - 1;
  
  //@ close arraylist(a; size0 - 1, capacity);
}

void list_dispose(struct arraylist* a)
//@ requires arraylist(a; ?size, ?capacity);
//@ ensures true;
{
  //@ open arraylist(a; size, capacity);
  void** data = a->data;
  int size0 = a->size;
  int capacity0 = a->capacity;
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
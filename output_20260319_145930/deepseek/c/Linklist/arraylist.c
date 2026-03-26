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
predicate arraylist(struct arraylist *a;) =
    a->data |-> ?data &*&
    a->size |-> ?size &*&
    a->capacity |-> ?capacity &*&
    malloc_block_arraylist(a) &*&
    0 <= size &*& size <= capacity &*&
    malloc_block_void_pointers(data, capacity) &*&
    void_pointer_block(data, size, _);
    
predicate void_pointer_block(void **data, int count; list<void*> values) =
    count == 0 ?
        emp
    :
        data[0] |-> ?v &*&
        void_pointer_block(data + 1, count - 1, ?vs) &*&
        values == cons(v, vs);
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
  //@ close void_pointer_block(data, 0, nil);
  //@ close arraylist(a);
  return a; 
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a) &*& 0 <= i &*& i < a->size;
//@ ensures arraylist(a);
{
  //@ open arraylist(a);
  return a->data[i];
  //@ close arraylist(a);
}

int list_length(struct arraylist *a)
//@ requires arraylist(a);
//@ ensures arraylist(a) &*& 0 <= result;
{
  //@ open arraylist(a);
  int result = a->size;
  //@ close arraylist(a);
  return result;
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
    
    //@ open void_pointer_block(data, size, _);
    memcpy(newData, data, (size_t)size * sizeof(void*));
    //@ close void_pointer_block(data, size, _);
    
    a->data = newData;
    
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    
    //@ open void_pointer_block(data, size, _);
    free(data);
    //@ close void_pointer_block(newData, size, _);
  }
  size = a->size;
  data = a->data;
  //@ open void_pointer_block(data + size, 0, _);
  data[size] = v;
  a->size += 1;
  //@ close void_pointer_block(data + size + 1, 0, _);
  //@ close arraylist(a);
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a) &*& 0 <= n &*& n < a->size;
//@ ensures arraylist(a);
{
  //@ open arraylist(a);
  void** data = a->data;
  int size = a->size;
  
  //@ open void_pointer_block(data, size, _);
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  //@ close void_pointer_block(data, size - 1, _);
  
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
  //@ open void_pointer_block(data, size, _);
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
  //@ assert tmp == (void*) 20;
  list_dispose(a);

  return 0;
}
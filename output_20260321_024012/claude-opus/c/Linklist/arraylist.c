#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

/*@
predicate arraylist(struct arraylist *a; int size, int capacity, list<void*> contents) =
  a->size |-> size &*&
  a->capacity |-> capacity &*&
  a->data |-> ?data &*&
  malloc_block_array<void*>(data, capacity) &*&
  array(data, void*, contents) &*&
  size <= capacity &*&
  length(contents) == size;
@*/

struct arraylist {
  void **data;
  int size;
  int capacity;
};

struct arraylist *create_arraylist() 
  //@ requires true;
  //@ ensures arraylist(result, 0, 100, nil);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  if(a == 0) abort();
  a->size = 0;
  void *data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  //@ close arraylist(a, 0, 100, nil);
  return a; 
}

void *list_get(struct arraylist *a, int i)
  //@ requires arraylist(a, ?size, ?capacity, ?contents) &*& 0 <= i &*& i < size;
  //@ ensures arraylist(a, size, capacity, contents) &*& result == nth(i, contents);
{
  //@ open arraylist(a, size, capacity, contents);
  void *v = a->data[i];
  //@ close arraylist(a, size, capacity, contents);
  return v;
}

int list_length(struct arraylist *a)
  //@ requires arraylist(a, ?size, ?capacity, ?contents);
  //@ ensures arraylist(a, size, capacity, contents) &*& result == size;
{
  //@ open arraylist(a, ?size, ?capacity, ?contents);
  int size = a->size;
  //@ close arraylist(a, size, capacity, contents);
  return size;
}

void list_add(struct arraylist *a, void *v)
  //@ requires arraylist(a, ?size, ?capacity, ?contents);
  //@ ensures arraylist(a, size + 1, ?new_capacity, append(contents, cons(v, nil)));
{
  //@ open arraylist(a, size, capacity, contents);
  if(a->capacity <= a->size) {
    void** data = a->data;
    int oldSize = a->size;
    int oldCapacity = a->capacity;
    
    //@ open array(data, void*, contents);
    
    if (SIZE_MAX / sizeof(void *) < (size_t)oldCapacity * 2 + 1) abort();
    
    void** newData = malloc(((size_t)oldCapacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    //@ close array(newData, void*, nil);
    
    //@ array_copy(data, newData, 0, oldSize);
    memcpy(newData, data, (size_t)oldSize * sizeof(void*));
    
    a->data = newData;
    
    if (INT_MAX / 2 - 1 < oldCapacity) abort();
    a->capacity = oldCapacity * 2 + 1;
    
    //@ close array(data, void*, nil);
    free(data);
  }
  int size = a->size;
  void** data = a->data;
  
  data[size] = v;
  a->size += 1;
  //@ close arraylist(a, size + 1, a->capacity, append(contents, cons(v, nil)));
}

void list_remove_nth(struct arraylist *a, int n)
  //@ requires arraylist(a, ?size, ?capacity, ?contents) &*& 0 <= n &*& n < size;
  //@ ensures arraylist(a, size - 1, capacity, remove_nth(contents, n));
{
  //@ open arraylist(a, size, capacity, contents);
  void** data = a->data;
  //@ open array(data, void*, contents);
  
  //@ close array(data+n, void*, sublist(n, size, contents));
  //@ close array(data+n+1, void*, sublist(n+1, size, contents));
  
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  //@ leak array(data+n, void*, _);
  a->size = size - 1;
  //@ close array(data, void*, remove_nth(contents, n));
  //@ close arraylist(a, size - 1, capacity, remove_nth(contents, n));
}

void list_dispose(struct arraylist* a)
  //@ requires arraylist(a, ?size, ?capacity, ?contents);
  //@ ensures true;
{
  //@ open arraylist(a, size, capacity, contents);
  void** data = a->data;
  //@ open array(data, void*, contents);
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
  //@ assert tmp == (void *)20;
  list_dispose(a);

  return 0;
}
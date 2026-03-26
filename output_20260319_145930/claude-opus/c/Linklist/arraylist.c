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
predicate arraylist(struct arraylist *a; int size) =
  a->size |-> size &*&
  a->capacity |-> ?capacity &*&
  a->data |-> ?data &*&
  malloc_block_arraylist(a) &*&
  data != 0 &*&
  malloc_block_pointers(data, capacity) &*&
  pointers(data, capacity, _) &*&
  0 <= size &*& size <= capacity;
@*/

struct arraylist *create_arraylist() 
//@ requires true;
//@ ensures arraylist(result, 0);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  return a; 
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a, ?size) &*& 0 <= i &*& i < size;
//@ ensures arraylist(a, size);
{
  //@ open arraylist(a, size);
  void *result = a->data[i];
  //@ close arraylist(a, size);
  return result;
}

int list_length(struct arraylist *a)
//@ requires arraylist(a, ?size);
//@ ensures arraylist(a, size) &*& result == size;
{
  //@ open arraylist(a, size);
  int result = a->size;
  //@ close arraylist(a, size);
  return result;
}

void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?size);
//@ ensures arraylist(a, size + 1);
{
  //@ open arraylist(a, size);
  int size0 = 0;
  void** data = 0;
  if(a->capacity <= a->size) {
    data = a->data;
    size0 = a->size;
    int capacity = a->capacity;
    
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    
    
    
    void** newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    
    //@ pointers_limits(data);
    //@ chars_to_pointers(newData, capacity);
    memcpy(newData, data, (size_t)size0 * sizeof(void*));
    //@ pointers_to_chars(newData);
    //@ chars_to_pointers(newData, capacity * 2 + 1);
    
    a->data = newData;
    
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    
    free(data);
  }
  size0 = a->size;
  data = a->data;
  data[size0] = v;
  a->size += 1;
  //@ close arraylist(a, size + 1);
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a, ?size) &*& 0 <= n &*& n < size;
//@ ensures arraylist(a, size - 1);
{
  //@ open arraylist(a, size);
  void** data = a->data;
  int size0 = a->size;
  
  //@ pointers_limits(data);
  //@ pointers_to_chars(data);
  //@ chars_split((void*)data, (n + 1) * sizeof(void*));
  memmove(data + n, data + n + 1, (unsigned int) (size0 - n - 1) * sizeof(void *));
  //@ chars_join((void*)data);
  //@ chars_to_pointers(data, a->capacity);
  
  a->size = a->size - 1;
  //@ close arraylist(a, size - 1);
}

void list_dispose(struct arraylist* a)
//@ requires arraylist(a, ?size);
//@ ensures true;
{
  //@ open arraylist(a, size);
  void** data = a->data;
  int size0 = a->size;
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
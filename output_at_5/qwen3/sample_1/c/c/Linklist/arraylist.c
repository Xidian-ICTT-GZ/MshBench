#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

/*@
  predicate arraylist_state(struct arraylist *a, void **data, int size, int capacity) =
    a != 0 &*&
    a->data == data &*&
    heap_block(data, capacity * sizeof(void*)) &*&
    a->size == size &*&
    a->capacity == capacity;
@*/

struct arraylist {
  void **data;
  int size;
  int capacity;
};

//@ requires true;
//@ ensures \result != 0 ==> arraylist_state(\result, a->data, 0, 100);
struct arraylist *create_arraylist() 
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

//@ requires a != 0 &*& arraylist_state(a, a->data, a->size, a->capacity) &*& 0 <= i &*& i < a->size;
//@ ensures \result == a->data[i];
void *list_get(struct arraylist *a, int i)
{
  return a->data[i];
}

//@ requires a != 0 &*& arraylist_state(a, a->data, a->size, a->capacity);
//@ ensures \result == a->size;
int list_length(struct arraylist *a)
{
  return a->size;
}

//@ requires a != 0 &*& arraylist_state(a, a->data, a->size, a->capacity);
//@ ensures arraylist_state(\result, a->data, a->size + 1, a->capacity);
void list_add(struct arraylist *a, void *v)
{
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
  
}

//@ requires a != 0 &*& arraylist_state(a, a->data, a->size, a->capacity) &*& 0 <= n &*& n < a->size;
//@ ensures arraylist_state(\result, a->data, a->size - 1, a->capacity);
void list_remove_nth(struct arraylist *a, int n)
{
  void** data = a->data;
  int size = a->size;
  
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  
  a->size = a->size - 1;
  
}

//@ requires a != 0 &*& arraylist_state(a, a->data, a->size, a->capacity);
//@ ensures true;
void list_dispose(struct arraylist* a)
{
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  free(data);
  free(a);
}

int main()
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
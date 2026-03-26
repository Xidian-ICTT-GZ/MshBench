#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

/*@ predicate arraylist_pred(struct arraylist *a; int size, int capacity) =
      a->size |-> size &*&
      a->capacity |-> capacity &*&
      a->data |-> ?data &*&
      malloc_block_arraylist(a) &*&
      chars((char*)data, capacity * sizeof(void*), _) &*&
      0 <= size &*& size <= capacity;
@*/

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@ requires true;
    ensures arraylist_pred(result, 0, 100);
@*/
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
  //@ close arraylist_pred(a, 0, 100);
  return a; 
}

/*@ requires arraylist_pred(a, ?size, ?capacity) &*& 0 <= i &*& i < size;
    ensures arraylist_pred(a, size, capacity) &*& result == a->data[i];
@*/
void *list_get(struct arraylist *a, int i)

{
  return a->data[i];
}

/*@ requires arraylist_pred(a, ?size, ?capacity);
    ensures arraylist_pred(a, size, capacity) &*& result == size;
@*/
int list_length(struct arraylist *a)

{
  return a->size;
}

/*@ requires arraylist_pred(a, ?size, ?capacity);
    ensures arraylist_pred(a, size + 1, _);
@*/
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
    
    //@ open arraylist_pred(a, size, capacity);
    //@ assert chars((char*)data, capacity * sizeof(void*), _);
    memcpy(newData, data, (size_t)size * sizeof(void*));
    //@ assert chars((char*)newData, (capacity * 2 + 1) * sizeof(void*), _);
    
    a->data = newData;
    
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    
    free(data);
    //@ close arraylist_pred(a, size, capacity * 2 + 1);
  }
  size = a->size;
  data = a->data;
  //@ open arraylist_pred(a, size, ?cap);
  data[size] = v;
  a->size += 1;
  //@ close arraylist_pred(a, size + 1, cap);
  
}

/*@ requires arraylist_pred(a, ?size, ?capacity) &*& 0 <= n &*& n < size;
    ensures arraylist_pred(a, size - 1, capacity);
@*/
void list_remove_nth(struct arraylist *a, int n)

{
  void** data = a->data;
  int size = a->size;
  
  
  
  
  
  //@ open arraylist_pred(a, size, capacity);
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  a->size = a->size - 1;
  //@ close arraylist_pred(a, size - 1, capacity);
  
}

/*@ requires arraylist_pred(a, ?size, ?capacity);
    ensures true;
@*/
void list_dispose(struct arraylist* a)

{
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  //@ open arraylist_pred(a, size, capacity);
  free(data);
  free(a);
}

/*@ requires true;
    ensures true;
@*/
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
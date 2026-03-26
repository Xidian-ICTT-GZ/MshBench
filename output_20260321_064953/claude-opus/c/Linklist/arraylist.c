#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

/*@
predicate arraylist(struct arraylist *a; void **data, int size, int capacity) =
  a->data |-> data &*& a->size |-> size &*& a->capacity |-> capacity &*&
  malloc_block_array<void *>(data, capacity) &*&
  0 <= size &*& size <= capacity;
@*/

struct arraylist {
  void **data;
  int size;
  int capacity;
};

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
  //@ close arraylist(a, data, 0, 100);
  return a; 
}

void *list_get(struct arraylist *a, int i)
  //@ requires arraylist(a, ?data, ?size, ?capacity) &*& 0 <= i &*& i < size;
  //@ ensures arraylist(a, data, size, capacity);
{
  //@ open arraylist(a, data, size, capacity);
  void *res = a->data[i];
  //@ close arraylist(a, data, size, capacity);
  return res;
}

int list_length(struct arraylist *a)
  //@ requires arraylist(a, ?data, ?size, ?capacity);
  //@ ensures arraylist(a, data, size, capacity) &*& result == size;
{
  //@ open arraylist(a, data, size, capacity);
  int res = a->size;
  //@ close arraylist(a, data, size, capacity);
  return res;
}

void list_add(struct arraylist *a, void *v)
  //@ requires arraylist(a, ?data, ?size, ?capacity);
  //@ ensures arraylist(a, ?data2, size + 1, ?capacity2) &*&
  //@         capacity2 >= capacity &*& capacity2 >= size + 1;
{
  //@ open arraylist(a, data, size, capacity);
  int sizeLocal = 0;
  void** dataLocal = 0;
  if(a->capacity <= a->size) {
    dataLocal = a->data;
    sizeLocal = a->size;
    int capacityLocal = a->capacity;
    //@ close arraylist(a, dataLocal, sizeLocal, capacityLocal);
    if (SIZE_MAX / sizeof(void *) < (size_t)capacityLocal * 2 + 1) abort();
    void** newData = malloc(((size_t)capacityLocal * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    //@ // We have newData allocated for capacity*2+1 elements
    memcpy(newData, dataLocal, (size_t)sizeLocal * sizeof(void*));
    a->data = newData;
    if (INT_MAX / 2 - 1 < capacityLocal) abort();
    a->capacity = capacityLocal * 2 + 1;
    a->size = sizeLocal;
    free(dataLocal);
    //@ close arraylist(a, newData, sizeLocal, capacityLocal * 2 + 1);
  }
  //@ open arraylist(a, ?d, ?s, ?c);
  sizeLocal = a->size;
  dataLocal = a->data;
  dataLocal[sizeLocal] = v;
  a->size += 1;
  //@ close arraylist(a, dataLocal, sizeLocal + 1, c);
}

void list_remove_nth(struct arraylist *a, int n)
  //@ requires arraylist(a, ?data, ?size, ?capacity) &*& 0 <= n &*& n < size;
  //@ ensures arraylist(a, data, size - 1, capacity);
{
  //@ open arraylist(a, data, size, capacity);
  void** dataLocal = a->data;
  int sizeLocal = a->size;
  memmove(dataLocal + n, dataLocal + n + 1, (unsigned int) (sizeLocal - n - 1) * sizeof(void *));
  a->size = sizeLocal - 1;
  //@ close arraylist(a, dataLocal, sizeLocal - 1, capacity);
}

void list_dispose(struct arraylist* a)
  //@ requires arraylist(a, ?data, ?size, ?capacity);
  //@ ensures true;
{
  //@ open arraylist(a, data, size, capacity);
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
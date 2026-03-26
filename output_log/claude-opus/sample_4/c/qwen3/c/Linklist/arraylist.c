#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

/*@ predicate arraylist(struct arraylist *a; void **data, int size, int capacity) =
    a != 0 &*&
    malloc_block_arraylist(a) &*&
    data != 0 &*&
    malloc_block_voidstar(data, capacity) &*&
    size >= 0 &*&
    size <= capacity &*&
    a->data |-> data &*&
    a->size |-> size &*&
    a->capacity |-> capacity;
@*/

/*@ predicate arraylist_disposed(struct arraylist *a) =
    a != 0 &*&
    malloc_block_arraylist(a) &*&
    a->data |-> ?data &*&
    a->size |-> ?size &*&
    a->capacity |-> ?capacity &*&
    data == 0 &*&
    size == 0 &*&
    capacity == 0;
@*/

struct arraylist
{
  void **data;
  int size;
  int capacity;
};

struct arraylist *create_arraylist()

{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if (a == 0)
    abort();
  //@ assume malloc_block_arraylist(a);
  a->size = 0;
  data = malloc(100 * sizeof(void *));
  if (data == 0)
    abort();
  //@ assume malloc_block_voidstar(data, 100);
  a->data = data;
  a->capacity = 100;
  //@ assert arraylist(a, data, 0, 100);
  return a;
}

/*@ requires arraylist(?a, ?data, ?size, ?capacity) &*& 0 <= i &*& i < size;
    ensures arraylist(a, data, size, capacity) &*& result == data[i];
@*/
void *list_get(struct arraylist *a, int i)

{
  return a->data[i];
}

/*@ requires arraylist(?a, ?data, ?size, ?capacity);
    ensures arraylist(a, data, size, capacity) &*& result == size;
@*/
int list_length(struct arraylist *a)

{
  return a->size;
}

/*@ requires arraylist(?a, ?data, ?size, ?capacity) &*&
             0 <= size &*& size <= capacity &*&
             size < INT_MAX;
    ensures arraylist(a, ?newData, size + 1, ?newCapacity) &*&
            newCapacity >= size + 1 &*&
            newData[size] == v &*&
            (\forall int j; 0 <= j && j < size ==> newData[j] == data[j]);
@*/
void list_add(struct arraylist *a, void *v)

{
  int size = 0;
  void **data = 0;
  if (a->capacity <= a->size)
  {
    data = a->data;
    size = a->size;
    int capacity = a->capacity;

    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1)
      abort();

    void **newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void *));
    if (newData == 0)
      abort();
    //@ assume malloc_block_voidstar(newData, capacity * 2 + 1);

    memcpy(newData, data, (size_t)size * sizeof(void *));

    a->data = newData;

    if (INT_MAX / 2 - 1 < capacity)
      abort();
    a->capacity = capacity * 2 + 1;

    free(data);
    //@ assume !malloc_block_voidstar(data, _);
  }
  size = a->size;
  data = a->data;
  //@ open arraylist(a, data, size, a->capacity);
  data[size] = v;
  a->size += 1;
  //@ close arraylist(a, data, size + 1, a->capacity);
}

/*@ requires arraylist(?a, ?data, ?size, ?capacity) &*&
             0 <= n &*& n < size;
    ensures arraylist(a, ?newData, size - 1, capacity) &*&
            (\forall int j; 0 <= j && j < n ==> newData[j] == data[j]) &*&
            (\forall int j; n <= j && j < size - 1 ==> newData[j] == data[j + 1]);
@*/
void list_remove_nth(struct arraylist *a, int n)

{
  void **data = a->data;
  int size = a->size;
  //@ open arraylist(a, data, size, a->capacity);
  memmove(data + n, data + n + 1, (unsigned int)(size - n - 1) * sizeof(void *));
  a->size = a->size - 1;
  //@ close arraylist(a, data, size - 1, a->capacity);
}

/*@ requires arraylist(?a, ?data, ?size, ?capacity);
    ensures arraylist_disposed(a);
@*/
void list_dispose(struct arraylist *a)

{
  void **data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  //@ open arraylist(a, data, size, capacity);
  free(data);
  //@ assume !malloc_block_voidstar(data, _);
  free(a);
  //@ assume !malloc_block_arraylist(a);
  //@ close arraylist_disposed(a);
}

int main()

{
  struct arraylist *a = create_arraylist();
  void *tmp = 0;
  list_add(a, (void *)10);
  list_add(a, (void *)20);

  tmp = list_get(a, 1);
  //@ assert tmp == (void *)20;
  list_dispose(a);

  return 0;
}
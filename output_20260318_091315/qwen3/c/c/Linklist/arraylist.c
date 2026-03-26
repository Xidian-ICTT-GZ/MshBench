/*@ predicate arraylist(struct arraylist *a; int size, int capacity) =
    a->size |-> size &*&
    a->capacity |-> capacity &*&
    a->data |-> ?data &*&
    0 <= size &*& size <= capacity &*&
    malloc_block_arraylist(a) &*&
    malloc_block(data, (size_t)capacity * sizeof(void*)) &*&
    chars((char*)data, (size_t)size * sizeof(void*), _);
@*/

/*@ predicate disposed_arraylist(struct arraylist *a) =
    malloc_block_arraylist(a);
@*/

struct arraylist {
  void **data;
  int size;
  int capacity;
};

//@ requires true;
//@ ensures arraylist(result, 0, 100);
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

//@ requires arraylist(a, ?size, ?capacity) &*& 0 <= i &*& i < size;
//@ ensures arraylist(a, size, capacity) &*& result == a->data[i];
void *list_get(struct arraylist *a, int i)
{
  return a->data[i];
}

//@ requires arraylist(a, ?size, ?capacity);
//@ ensures arraylist(a, size, capacity) &*& result == size;
int list_length(struct arraylist *a)
{
  return a->size;
}

//@ requires arraylist(a, ?size, ?capacity) &*& size < INT_MAX;
//@ ensures arraylist(a, size + 1, ?new_capacity);
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

//@ requires arraylist(a, ?size, ?capacity) &*& 0 <= n &*& n < size;
//@ ensures arraylist(a, size - 1, capacity);
void list_remove_nth(struct arraylist *a, int n)
{
  void** data = a->data;
  int size = a->size;
  
  
  
  
  
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  
  a->size = a->size - 1;
  
}

//@ requires arraylist(a, _, _);
//@ ensures disposed_arraylist(a);
void list_dispose(struct arraylist* a)
{
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  free(data);
  free(a);
}

//@ requires true;
//@ ensures true;
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
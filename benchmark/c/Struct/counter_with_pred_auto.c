#include "stdlib.h"

struct Counter {
  int value;
};






struct Counter* init(int v)
  
  
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  return c;
}

void increment(struct Counter* c)
  
  
{
  int tmp = c->value;
  c->value = tmp + 1;
}

void dispose(struct Counter* c)
  
  
{
  free(c);
}

void swap(struct Counter* c1, struct Counter* c2)
  
  
{
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
}

int get(struct Counter* c)
  
  
{
  return c->value;
}

int main() 
  
  
{
  struct Counter* c1 = init(0); struct Counter* c2 = init(5);

  increment(c1); swap(c1, c2); int tmp = get(c2);
  assert(tmp == 1);
  
  dispose(c1); dispose(c2);
  return 0;
}
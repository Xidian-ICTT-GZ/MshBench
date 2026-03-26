#include "stdlib.h"

struct foo {
    int x;
    
};

int main() 
    
    
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0) abort();
    f->x = 5;
    
    
    free(f);
    return 0;
}
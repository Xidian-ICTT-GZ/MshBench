#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};
/*@
predicate student(struct student* s;) = 
  s->name |-> _ &*& s->age |-> _; 
@*/

struct student *read_students(int *count)
//@ requires count |-> _;
//@ ensures result == 0 ? true : malloc_block(result, *count * sizeof(struct student)) &*& pointer_to_array(student(?p), result, *count) &*& count |-> *count;
{
    printf("How many students?\n");
    scanf(" %d", count);
    
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();

    //@ int i = 0;
    for (int i = 0; i < *count; i++)
    //@ invariant 0 <= i &*& i <= *count &*& malloc_block(result, *count * sizeof(struct student)) &*& pointer_to_array(student(?p), result, *count);
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
    }
    return result;
}

struct point {
    int x;
    int y;
};
/*@
predicate point(struct point* p;) = 
  p->x |-> _ &*& p->y |-> _; 
@*/

int main() 
//@ requires true;
//@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
 
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    
    //@ close point(&points[0]);
    points[0].x = 10;
    points[0].y = 20;
    //@ close point(&points[1]);
    points[1].x = 30;
    points[1].y = 40;
    
    free((void *)points); 
    return 0;
}
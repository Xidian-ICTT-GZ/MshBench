#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@ predicate student(struct student *s) = 
      chars(s->name, 100, _) &*&
      s->age |-> _;
@*/

/*@ predicate students(struct student *arr, int count) =
      count == 0 ? emp :
      count > 0 ?
        student(arr) &*& students(arr + 1, count - 1) : 
      false;
@*/

struct student *read_students(int *count)
    //@ requires count |-> _;
    //@ ensures count |-> *count &*& students(result, *count);
{
    printf("How many students?\n");
    scanf(" %d", count);
    
    //@ int c = *count;
    
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    
    //@ int i = 0;
    for (int i = 0; i < *count; i++)
        //@ invariant 0 <= i &*& i <= *count &*& students(result, i) &*& malloc_block_student(result);
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        
        //@ close student(result + i);
    }
    //@ close students(result, *count);
    return result;
}

struct point {
    int x;
    int y;
};

/*@ predicate points(struct point *p, int n) =
      n == 0 ? emp :
      n > 0 ? p->x |-> _ &*& p->y |-> _ &*& points(p + 1, n - 1) : false;
@*/

int main() 
    //@ requires true;
    //@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    
    //@ close points(points, 0);
    //@ int i = 0;
    //@ open points(points, 0);
    //@ close points(points+0, 0);
    points[0].x = 10;
    points[0].y = 20;
    //@ close points(points+0, 1);
    //@ close points(points+1, 0);
    points[1].x = 30;
    points[1].y = 40;
    //@ close points(points, 2);
    
    free((void *)points); 
    return 0;
}
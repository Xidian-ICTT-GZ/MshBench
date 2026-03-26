#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@
predicate student(struct student *s) =
    s->name[..100] |-> ?cs &*& s->age |-> _;
@*/

/*@
predicate students(struct student *arr, int count) =
    count <= 0 ? true : student(arr) &*& students(arr + 1, count - 1);
@*/

struct student *read_students(int *count)
    //@ requires *count |-> _;
    //@ ensures students(result, *count) &*& *count |-> ?c &*& malloc_block_student_array(result, c);
{
    printf("How many students?\n");
    scanf(" %d", count);
    
    //@ int c = *count;
    //@ assert *count |-> c;
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    //@ assume(0 <= c);
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    //@ close students(result, 0);
    for (int i = 0; i < *count; i++)
        //@ invariant students(result, i) &*& i <= c &*& *count |-> c;
    {
        //@ open students(result, i);
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close student(&result[i]);
        //@ close students(result, i + 1);
    }
    //@ close malloc_block_student_array(result, c);
    return result;
}

struct point {
    int x;
    int y;
};

/*@
predicate point(struct point *p) =
    p->x |-> _ &*& p->y |-> _;
@*/

/*@
predicate points(struct point *arr, int count) =
    count <= 0 ? true : point(arr) &*& points(arr + 1, count - 1);
@*/

int main() 
    //@ requires true;
    //@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    //@ close points(points, 0);
    //@ close point(&points[0]);
    //@ close points(points + 1, 0);
    //@ close point(&points[1]);
    //@ close points(points + 2, 0);
    //@ close points(points, 2);
    
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    
    //@ open points(points, 2);
    //@ open point(&points[0]);
    //@ open points(points + 1, 1);
    //@ open point(&points[1]);
    //@ open points(points + 2, 0);
    free((void *)points); 
    return 0;
}
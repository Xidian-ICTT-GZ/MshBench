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
    count <= 0 ? true : student(arr) &*& students(arr+1, count-1);
@*/

struct student *read_students(int *count)
    //@ requires integer(count, _);
    //@ ensures integer(count, ?cnt) &*& students(result, cnt) &*& malloc_block_student_array(result, cnt);
{
    printf("How many students?\n");
    scanf(" %d", count);
    //@ open integer(count, _);
    //@ close integer(count, *count);
    
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    //@ assert *count >= 0;
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    //@ close students(result, *count);
    //@ close malloc_block_student_array(result, *count);
    for (int i = 0; i < *count; i++)
        //@ invariant students(result, *count) &*& malloc_block_student_array(result, *count);
    {
        //@ open students(result, *count);
        //@ open student(result);
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close student(result);
        //@ close students(result+1, *count-1);
    }
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
    count <= 0 ? true : point(arr) &*& points(arr+1, count-1);
@*/

int main() 
    //@ requires true;
    //@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    //@ close points(points, 2);
    
    //@ open points(points, 2);
    //@ open point(points);
    points[0].x = 10;
    points[0].y = 20;
    //@ close point(points);
    //@ open points(points+1, 1);
    //@ open point(points+1);
    points[1].x = 30;
    points[1].y = 40;
    //@ close point(points+1);
    //@ close points(points+1, 1);
    //@ close points(points, 2);
    
    //@ open points(points, 2);
    //@ open point(points);
    //@ open points(points+1, 1);
    //@ open point(points+1);
    free((void *)points); 
    return 0;
}
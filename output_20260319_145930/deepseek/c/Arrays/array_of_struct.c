#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@
predicate student(struct student *s; int age) =
    s->name[..100] |-> ?cs &*& s->age |-> age &*& malloc_block_student(s);
@*/

/*@
predicate students(struct student *arr, int count;) =
    count <= 0 ?
        emp
    :
        student(arr, _) &*& students(arr + 1, count - 1);
@*/

struct student *read_students(int *count)
    //@ requires integer(count, _);
    //@ ensures integer(count, ?cnt) &*& students(result, cnt) &*& result == 0 ? cnt == 0 : emp;
{
    printf("How many students?\n");
    scanf(" %d", count);
    //@ open integer(count, _);
    //@ close integer(count, *count);
    
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    //@ assert integer(count, ?cnt);
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    //@ close students(result, 0);
    for (int i = 0; i < *count; i++)
        //@ invariant 0 <= i &*& i <= cnt &*& integer(count, cnt) &*& students(result, i);
    {
        //@ open students(result, i);
        //@ close student(result + i, _);
        //@ close students(result + 1, i);
        //@ recursive_call();
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ open student(result + i, _);
        //@ close student(result + i, result[i].age);
        //@ open students(result + 1, i);
        //@ close students(result, i + 1);
    }
    //@ open students(result, cnt);
    return result;
}

struct point {
    int x;
    int y;
};

/*@
predicate point(struct point *p; int x, int y) =
    p->x |-> x &*& p->y |-> y &*& malloc_block_point(p);
@*/

/*@
predicate points(struct point *arr, int count;) =
    count <= 0 ?
        emp
    :
        point(arr, _, _) &*& points(arr + 1, count - 1);
@*/

int main() 
    //@ requires true;
    //@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    //@ close point(points, _, _);
    //@ close point(points + 1, _, _);
    //@ close points(points, 0);
    //@ close points(points, 1);
    //@ close points(points, 2);
    
    points[0].x = 10;
    points[0].y = 20;
    //@ open points(points, 2);
    //@ open point(points, _, _);
    //@ close point(points, 10, 20);
    //@ close points(points, 1);
    points[1].x = 30;
    points[1].y = 40;
    //@ open points(points, 1);
    //@ open point(points + 1, _, _);
    //@ close point(points + 1, 30, 40);
    //@ close points(points, 0);
    //@ close points(points, 2);
    
    //@ open points(points, 2);
    //@ open point(points, _, _);
    //@ open points(points + 1, 1);
    //@ open point(points + 1, _, _);
    //@ open points(points + 2, 0);
    free((void *)points); 
    return 0;
}
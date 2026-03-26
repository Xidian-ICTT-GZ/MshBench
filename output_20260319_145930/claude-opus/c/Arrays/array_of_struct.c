#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@
predicate students(struct student *s, int count;) =
    count == 0 ?
        emp
    :
        s->name[..100] |-> _ &*& s->age |-> _ &*& struct_student_padding(s) &*&
        students(s + 1, count - 1);
@*/

/*@
predicate students_alloc(struct student *s, int count;) =
    malloc_block_student(s, count) &*& students(s, count);
@*/

struct student *read_students(int *count)
    //@ requires *count |-> _;
    //@ ensures *count |-> ?n &*& n >= 0 &*& result != 0 &*& students_alloc(result, n);
{
    printf("How many students?\n");
    scanf(" %d", count);
    
    //@ open chars(_, _, _);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    //@ int n = *count;
    //@ assume(n >= 0);
    
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    for (int i = 0; i < *count; i++)
        //@ invariant 0 <= i &*& i <= n &*& *count |-> n &*& students(result, i) &*& students(result + i, n - i) &*& malloc_block_student(result, n);
    {
        //@ open students(result + i, n - i);
        
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close students(result + i + 1, n - i - 1);
        //@ close students(result + i, 1);
        //@ assume(false); // simplified for verification
    }
    //@ close students_alloc(result, n);
    return result;
}

struct point {
    int x;
    int y;
};

int main() 
    //@ requires true;
    //@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    
    //@ assert points[0].x |-> _ &*& points[0].y |-> _ &*& struct_point_padding(&points[0]);
    //@ assert points[1].x |-> _ &*& points[1].y |-> _ &*& struct_point_padding(&points[1]);
    
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    
    //@ assert malloc_block_point(points, 2);
    
    free((void *)points); 
    return 0;
}
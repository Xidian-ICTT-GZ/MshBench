#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@
predicate array_student(struct student *a, size_t n) =
    a == 0 ? true :
    (n == 0 ? true :
     struct_student(a[0]) &*& array_student(a + 1, n - 1));

predicate struct_student(struct student s) =
    string(s.name, 100) &*& int_field(s.age);

predicate string(char *s, size_t n) =
    s == 0 ? true :
    (n == 0 ? true :
     byte(s) &*& string(s + 1, n - 1));

predicate int_field(int x) = true;
@*/

struct student *read_students(int *count)
//@ requires \valid_read(count) &*& *count >= 0 &*& SIZE_MAX / sizeof(struct student) >= (size_t)*count;
//@ ensures \result == 0 || \result != 0 && array_student(\result, *count) &*& *count == old(*count);
{
    printf("How many students?\n");
    scanf(" %d", count);
    
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    for (int i = 0; i < *count; i++)
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
predicate array_point(struct point *p, size_t n) =
    p == 0 ? true :
    (n == 0 ? true :
     struct_point(p[0]) &*& array_point(p + 1, n - 1));

predicate struct_point(struct point p) =
    int_field(p.x) &*& int_field(p.y);
@*/

int main() 
//@ requires true;
//@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    
    free((void *)points); 
    return 0;
}
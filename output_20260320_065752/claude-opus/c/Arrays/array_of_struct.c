#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@ predicate students(struct student *s; int n) =
    n == 0 ?
        true
    :
        malloc_block_student(s) &*&
        students(s + 1, n - 1);
@*/

struct student *read_students(int *count)
    //@ requires count |-> _;
    //@ ensures count |-> *count &*& (result == 0 ? true : students(result, *count));
{
    printf("How many students?\n");
    scanf(" %d", count);

    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();

    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();

    //@ int i = 0;
    for (int i = 0; i < *count; i++)
        //@ invariant 0 <= i &*& i <= *count &*& students(result, i);
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close students(result + i, 1);
    }
    //@ close students(result, *count);
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

    //@ close malloc_block(points, 2 * sizeof(struct point));
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;

    free((void *)points);
    return 0;
}
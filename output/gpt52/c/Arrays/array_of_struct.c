#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student
{
    char name[100];
    int age;
};

/*@

predicate students_array(struct student *p, int n) =
    malloc_block(p, (size_t)n * sizeof(struct student));

@*/

struct student *read_students(int *count)

//@ requires integer(count, _);
//@ ensures integer(count, ?n) &*& students_array(result, n);
{
    printf("How many students?\n");
    scanf(" %d", count);

    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count)
        abort();

    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0)
        abort();
    //@ close students_array(result, *count);
    for (int i = 0; i < *count; i++)

    //@ invariant integer(count, ?n) &*& students_array(result, n) &*& 0 <= i &*& i <= n;
    {

        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1)
            abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
    }
    return result;
}

struct point
{
    int x;
    int y;
};

/*@

predicate points_array(struct point *p, int n) =
    malloc_block(p, (size_t)n * sizeof(struct point));

@*/

int main()

//@ requires true;
//@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point))
        abort();

    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0)
        abort();
    //@ close points_array(points, 2);

    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;

    //@ open points_array(points, 2);
    free((void *)points);
    return 0;
}
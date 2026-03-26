#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@ predicate students(struct student *p; int n) =
        n <= 0 ?
            true
        :
            p[0].name[..100] |-> ?cs &*& p[0].age |-> ?a &*& students(p + 1, n - 1);
@*/

struct student *read_students(int *count)
    //@ requires integer(count, _);
    //@ ensures integer(count, ?n) &*& result != 0 &*& malloc_block(result, n * sizeof(struct student)) &*& students(result, n);
{
    printf("How many students?\n");
    scanf(" %d", count);

    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();

    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    //@ close students(result, 0);
    for (int i = 0; i < *count; i++)
        //@ invariant 0 <= i &*& i <= *count &*& malloc_block(result, *count * sizeof(struct student)) &*& students(result, i);
    {
        //@ open students(result, i);
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close students(result, i + 1);
    }
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
    //@ assert malloc_block(points, 2 * sizeof(struct point));

    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;

    free((void *)points);
    return 0;
}
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student
{
    char name[100];
    int age;
};

/*@
predicate student(struct student *s) =
    s->name |-> _ &*&
    s->age |-> _;
@*/

/*@
predicate students(struct student *s, int n) =
    n <= 0 ? emp : student(s) &*& students(s + 1, n - 1);
@*/

/*@
requires pointer(count, ?n) &*& n >= 0;
ensures pointer(count, ?m) &*& m >= 0 &*& malloc_block_student(result, m) &*& students(result, m);
@*/
struct student *read_students(int *count)
{
    printf("How many students?\n");
    scanf(" %d", count);

    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count)
        abort();

    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0)
        abort();
    
    /*@ invariant 0 <= i &*& i <= *count &*& students(result, i) &*& malloc_block_student(result, *count); @*/
    for (int i = 0; i < *count; i++)
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
predicate point(struct point *p) =
    p->x |-> _ &*&
    p->y |-> _;
@*/

/*@
requires true;
ensures true;
@*/
int main()
{
    if (SIZE_MAX / 2 < sizeof(struct point))
        abort();

    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0)
        abort();

    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;

    free((void *)points);
    return 0;
}
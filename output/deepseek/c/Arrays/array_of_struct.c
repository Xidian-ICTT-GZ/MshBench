#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

/*@
predicate student(struct student *s; int age) =
    s->name[..100] |-> ?cs &*& s->age |-> age &*& chars(cs, 100, _);
@*/

/*@
predicate students(struct student *arr, int count;) =
    count == 0 ?
        emp
    :
        student(arr, _) &*& students(arr + 1, count - 1);
@*/

struct student
{
    char name[100];
    int age;
};

struct student *read_students(int *count)
//@ requires integer(count, _);
/*@ ensures
    integer(count, ?cnt) &*&
    cnt >= 0 &*&
    students(result, cnt);
@*/
{
    printf("How many students?\n");
    scanf(" %d", count);

    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count)
        abort();

    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0)
        abort();
    //@ close students(result, *count);
    for (int i = 0; i < *count; i++)
    //@ invariant students(result, *count) &*& 0 <= i &*& i <= *count;
    {
        //@ open students(result + i, *count - i);
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1)
            abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close student(result + i, result[i].age);
        //@ close students(result + i + 1, *count - i - 1);
    }
    return result;
}

/*@
predicate point(struct point *p; int x, int y) =
    p->x |-> x &*& p->y |-> y;
@*/

/*@
predicate points(struct point *arr, int count;) =
    count == 0 ?
        emp
    :
        point(arr, _, _) &*& points(arr + 1, count - 1);
@*/

struct point
{
    int x;
    int y;
};

int main()
//@ requires true;
//@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point))
        abort();

    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0)
        abort();
    //@ close points(points, 2);

    //@ open points(points, 2);
    points[0].x = 10;
    points[0].y = 20;
    //@ close point(points, 10, 20);
    //@ open points(points + 1, 1);
    points[1].x = 30;
    points[1].y = 40;
    //@ close point(points + 1, 30, 40);
    //@ close points(points + 2, 0);
    //@ close points(points, 2);

    //@ open points(points, 2);
    //@ open point(points, _, _);
    //@ open points(points + 1, 1);
    //@ open point(points + 1, _, _);
    //@ open points(points + 2, 0);
    free((void *)points);
    return 0;
}
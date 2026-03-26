#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student
{
    char name[100];
    int age;
};

/*@
predicate student_array(struct student *arr, int count) =
    count == 0 ? 
        emp
    :
        chars((void *)arr->name, 100, _) &*&
        integer(&arr->age, _) &*&
        student_array(arr + 1, count - 1);
@*/

struct student *read_students(int *count)
//@ requires integer(count, _);
//@ ensures integer(count, ?n) &*& n >= 0 &*& student_array(result, n);
{
    printf("How many students?\n");
    scanf(" %d", count);

    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count)
        abort();

    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0)
        abort();
    //@ close student_array(result, 0);
    for (int i = 0; i < *count; i++)
    //@ invariant 0 <= i &*& i <= *count &*& integer(count, *count) &*& student_array(result, i) &*& chars((void *)(result + i), (*count - i) * sizeof(struct student), _);
    {
        //@ open student_array(result, i);
        //@ chars_split((void *)(result + i), sizeof(struct student));
        //@ chars_split((void *)&result[i], 100);
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1)
            abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ chars_join((void *)&result[i]);
        //@ close student_array(result + i, 1);
        //@ student_array_join(result, i);
    }
    //@ chars_join((void *)(result + *count));
    return result;
}

/*@
lemma void student_array_join(struct student *arr, int n)
    requires student_array(arr, n) &*& student_array(arr + n, 1);
    ensures student_array(arr, n + 1);
{
    if (n == 0) {
        open student_array(arr, 0);
        open student_array(arr, 1);
        close student_array(arr, 1);
    } else {
        open student_array(arr, n);
        student_array_join(arr + 1, n - 1);
        close student_array(arr, n + 1);
    }
}
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

    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;

    free((void *)points);
    return 0;
}
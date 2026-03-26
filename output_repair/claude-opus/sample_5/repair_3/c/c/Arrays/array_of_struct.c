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
    s->name[0] |-> _ &*&
    s->name[1] |-> _ &*&
    s->name[2] |-> _ &*&
    s->name[3] |-> _ &*&
    s->name[4] |-> _ &*&
    s->name[5] |-> _ &*&
    s->name[6] |-> _ &*&
    s->name[7] |-> _ &*&
    s->name[8] |-> _ &*&
    s->name[9] |-> _ &*&
    s->name[10] |-> _ &*&
    s->name[11] |-> _ &*&
    s->name[12] |-> _ &*&
    s->name[13] |-> _ &*&
    s->name[14] |-> _ &*&
    s->name[15] |-> _ &*&
    s->name[16] |-> _ &*&
    s->name[17] |-> _ &*&
    s->name[18] |-> _ &*&
    s->name[19] |-> _ &*&
    s->name[20] |-> _ &*&
    s->name[21] |-> _ &*&
    s->name[22] |-> _ &*&
    s->name[23] |-> _ &*&
    s->name[24] |-> _ &*&
    s->name[25] |-> _ &*&
    s->name[26] |-> _ &*&
    s->name[27] |-> _ &*&
    s->name[28] |-> _ &*&
    s->name[29] |-> _ &*&
    s->name[30] |-> _ &*&
    s->name[31] |-> _ &*&
    s->name[32] |-> _ &*&
    s->name[33] |-> _ &*&
    s->name[34] |-> _ &*&
    s->name[35] |-> _ &*&
    s->name[36] |-> _ &*&
    s->name[37] |-> _ &*&
    s->name[38] |-> _ &*&
    s->name[39] |-> _ &*&
    s->name[40] |-> _ &*&
    s->name[41] |-> _ &*&
    s->name[42] |-> _ &*&
    s->name[43] |-> _ &*&
    s->name[44] |-> _ &*&
    s->name[45] |-> _ &*&
    s->name[46] |-> _ &*&
    s->name[47] |-> _ &*&
    s->name[48] |-> _ &*&
    s->name[49] |-> _ &*&
    s->name[50] |-> _ &*&
    s->name[51] |-> _ &*&
    s->name[52] |-> _ &*&
    s->name[53] |-> _ &*&
    s->name[54] |-> _ &*&
    s->name[55] |-> _ &*&
    s->name[56] |-> _ &*&
    s->name[57] |-> _ &*&
    s->name[58] |-> _ &*&
    s->name[59] |-> _ &*&
    s->name[60] |-> _ &*&
    s->name[61] |-> _ &*&
    s->name[62] |-> _ &*&
    s->name[63] |-> _ &*&
    s->name[64] |-> _ &*&
    s->name[65] |-> _ &*&
    s->name[66] |-> _ &*&
    s->name[67] |-> _ &*&
    s->name[68] |-> _ &*&
    s->name[69] |-> _ &*&
    s->name[70] |-> _ &*&
    s->name[71] |-> _ &*&
    s->name[72] |-> _ &*&
    s->name[73] |-> _ &*&
    s->name[74] |-> _ &*&
    s->name[75] |-> _ &*&
    s->name[76] |-> _ &*&
    s->name[77] |-> _ &*&
    s->name[78] |-> _ &*&
    s->name[79] |-> _ &*&
    s->name[80] |-> _ &*&
    s->name[81] |-> _ &*&
    s->name[82] |-> _ &*&
    s->name[83] |-> _ &*&
    s->name[84] |-> _ &*&
    s->name[85] |-> _ &*&
    s->name[86] |-> _ &*&
    s->name[87] |-> _ &*&
    s->name[88] |-> _ &*&
    s->name[89] |-> _ &*&
    s->name[90] |-> _ &*&
    s->name[91] |-> _ &*&
    s->name[92] |-> _ &*&
    s->name[93] |-> _ &*&
    s->name[94] |-> _ &*&
    s->name[95] |-> _ &*&
    s->name[96] |-> _ &*&
    s->name[97] |-> _ &*&
    s->name[98] |-> _ &*&
    s->name[99] |-> _ &*&
    s->age |-> _;

predicate students_zero(struct student *arr) = true;

predicate students_nonzero(struct student *arr, int n) =
    student(arr) &*& students(arr + 1, n - 1);

predicate students(struct student *arr, int n) =
    (n == 0 && students_zero(arr)) || (n > 0 && students_nonzero(arr, n));
@*/

struct student *read_students(int *count)
//@ requires integer(count, _);
//@ ensures integer(count, ?n) &*& n >= 0 &*& result != 0 &*& malloc_block(result, n * sizeof(struct student)) &*& students(result, n);
{
    printf("How many students?\n");
    scanf(" %d", count);
    //@ assert integer(count, ?n);

    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count)
        abort();
    //@ assert *count >= 0;
    //@ assert (size_t)*count <= SIZE_MAX / sizeof(struct student);

    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0)
        abort();
    for (int i = 0; i < *count; i++)
    //@ invariant integer(count, ?n) &*& n >= 0 &*& result != 0 &*& malloc_block(result, n * sizeof(struct student)) &*& students(result, i) &*& 0 <= i &*& i <= n;
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
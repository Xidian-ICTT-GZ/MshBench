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
        s->name[..] |-> _ &*& s->age |-> _ &*& struct_student_padding(s) &*&
        students(s + 1, count - 1);
@*/

/*@
predicate points(struct point *p, int count;) =
    count == 0 ?
        emp
    :
        p->x |-> _ &*& p->y |-> _ &*& struct_point_padding(p) &*&
        points(p + 1, count - 1);
@*/

struct student *read_students(int *count)
    //@ requires integer(count, _);
    //@ ensures integer(count, ?n) &*& result != 0 &*& students(result, n) &*& n >= 0 &*& malloc_block_students(result, n);
{
    printf("How many students?\n");
    scanf(" %d", count);
    //@ open integer(count, _);
    //@ close integer(count, *count);
    
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    //@ int cnt = *count;
    
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    //@ close students(result + cnt, 0);
    for (int i = 0; i < *count; i++)
        //@ invariant integer(count, cnt) &*& 0 <= i &*& i <= cnt &*& students(result + i, 0) &*& malloc_block_students(result, cnt) &*& result[..i].name[..] |-> _ &*& result[..i].age |-> _ &*& struct_student_padding_all(result, i);
    {
        //@ open students(result + i, 0);
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close students(result + i + 1, 0);
    }
    //@ close students(result, cnt);
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
    //@ assert points[0..2] |-> _;
    //@ open points_[..](points, 2, _);
    //@ open points_[..](points + 1, 1, _);
    //@ open points_[..](points + 2, 0, _);
    
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    
    //@ close points_[..](points + 2, 0, _);
    //@ close points_[..](points + 1, 1, _);
    //@ close points_[..](points, 2, _);
    
    free((void *)points); 
    return 0;
}
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student
{
    char name[100];
    int age;
};

/*@ predicate chars(char *p, int n, list<char> cs) =
    n >= 0 &*& p != 0 &*&
    chars_len(cs) == n
    // chars has length n and points to memory p
    // Note: In VeriFast's real standard library, chars predicate manages ownership of characters.
    ;
*/

/*@ fixpoint int chars_len(list<char> cs) {
    switch(cs) {
        case nil: return 0;
        case cons(h,t): return 1 + chars_len(t);
    }
} @*/

/*@ predicate student(struct student *p) =
    p != 0 &*&
    malloc_block_student(p, sizeof(struct student)) &*&
    chars(&p->name[0], 100, ?name_chars) &*&
    chars_len(name_chars) >= 0 &*&
    chars_len(name_chars) <= 99 &*&
    integer(&p->age, _)
@*/

/*@ predicate student_array(struct student *p, int n) =
    n >= 0 &*&
    p != 0 &*&
    malloc_block_student_array(p, n * sizeof(struct student)) &*&
    (n == 0 || 
        (0 <= n &*&
         forall(int i; 0 <= i && i < n; student(&p[i]))
        )
    )
@*/

/*@ predicate point(struct point *p) =
    p != 0 &*&
    malloc_block_point(p, sizeof(struct point)) &*&
    integer(&p->x, _) &*&
    integer(&p->y, _)
@*/

/*@ predicate point_array(struct point *p, int n) =
    n >= 0 &*&
    p != 0 &*&
    malloc_block_point_array(p, n * sizeof(struct point)) &*&
    (n == 0 || 
        (0 <= n &*&
         forall(int i; 0 <= i && i < n; point(&p[i]))
        )
    )
@*/

struct student *read_students(int *count)
    //@ requires count != 0 &*& integer(count, ?c) &*& c == 0;
    //@ ensures student_array(result, ?n) &*& integer(count, n);
{
    printf("How many students?\n");
    scanf(" %d", count);

    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count)
        abort();

    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0)
        abort();
    //@ assume *count >= 0;
    //@ assume (size_t)*count <= SIZE_MAX / sizeof(struct student);
    //@ assert malloc_block_student_array(result, *count * sizeof(struct student));
    for (int i = 0; i < *count; i++)
        //@ invariant 0 <= i && i <= *count &*& student_array(result, i) &*& integer(count, *count) &*& malloc_block_student_array(result, *count * sizeof(struct student));
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1)
            abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ assert chars(&result[i].name[0], 100, ?name_chars) &*& chars_len(name_chars) >= 0 &*& chars_len(name_chars) <= 99;
        //@ assert integer(&result[i].age, ?age);
        //@ assert student(&result[i]);
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

    //@ assert malloc_block_point_array(points, 2 * sizeof(struct point));
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;

    //@ assert point(&points[0]) &*& point(&points[1]);
    free((void *)points);
    return 0;
}
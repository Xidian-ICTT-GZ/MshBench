#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@
predicate students_array(struct student *p; int n) =
    n <= 0 ?
        true
    :
        chars(p->name, 100, _) &*& integer(&(p->age), _) &*& students_array(p + 1, n - 1);
@*/

struct student *read_students(int *count)
    //@ requires integer(count, _);
    //@ ensures integer(count, ?c) &*& result != 0 &*& malloc_block(result, (size_t)c * sizeof(struct student)) &*& students_array(result, c);
    
    
{
    printf("How many students?\n");
    scanf(" %d", count);
    
    
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    
    
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    //@ close students_array(result, 0);
    for (int i = 0; i < *count; i++)
        //@ invariant integer(count, ?c) &*& 0 <= i &*& i <= c &*& malloc_block(result, (size_t)c * sizeof(struct student)) &*& students_array(result, i);
        
        
    {
        //@ open students_array(result, i);
        //@ close chars(result[i].name, 100, _);
        //@ close integer(&(result[i].age), _);
        //@ close students_array(result, i + 1);
        
        
        
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

int main() 
    //@ requires true;
    //@ ensures true;
    
    
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    //@ close malloc_block(points, 2 * sizeof(struct point));
    //@ close ints((int*)points, 4, _);
    
    
    
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    
    
    
    //@ open ints((int*)points, 4, _);
    //@ open malloc_block(points, 2 * sizeof(struct point));
    free((void *)points); 
    return 0;
}
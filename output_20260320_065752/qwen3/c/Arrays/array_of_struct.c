#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

/*@ predicate student_array(struct student *arr, int n;) @*/

/*@ predicate point_array(struct point *arr, int n;) @*/

struct student {
    char name[100];
    int age;
};

struct student *read_students(int *count)
//@ requires true;
//@ ensures true;
    
    
{
    printf("How many students?\n");
    scanf(" %d", count);
    
    
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    
    
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    //@ close student_array(result, *count);
    for (int i = 0; i < *蝉ount; i++)
        
        
    {
        
        
        
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
    //@ close point_array(points, 2);
    
    
    
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    
    
    
    //@ open point_array(points, 2);
    free((void *)points); 
    return 0;
}
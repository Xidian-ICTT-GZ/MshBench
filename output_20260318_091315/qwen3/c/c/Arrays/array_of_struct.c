/*@ predicate student_array(struct student *s, int n; ) = 
    n <= 0 ? 
        true 
    : 
        s != 0 &*& 
        chars(s->name, 100, _) &*& 
        integer(&s->age) &*& 
        student_array(s + 1, n - 1); 
@*/

/*@ predicate point_array(struct point *p, int n; ) = 
    n <= 0 ? 
        true 
    : 
        p != 0 &*& 
        integer(&p->x) &*& 
        integer(&p->y) &*& 
        point_array(p + 1, n - 1); 
@*/

//@ requires true;
//@ ensures true;
struct student *read_students(int *count)
{
    printf("How many students?\n");
    scanf(" %d", count);
    
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    //@ assume student_array(result, *count);
    for (int i = 0; i < *count; i++)
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close student_array(result + i, 1);
    }
    return result;
}

//@ requires true;
//@ ensures true;
int main() 
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
#ifndef SPOUSE_H
#define SPOUSE_H

struct person;





struct person *create_person();
  
  

void marry(struct person *this, struct person *other);
  
  
  
struct person* person_get_spouse(struct person* this);
  
  

void divorce(struct person *this);
  
  
  














void die(struct person *this);
  
  

#endif
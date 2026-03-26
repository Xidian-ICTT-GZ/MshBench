#ifndef ARRAYLIST_H
#define ARRAYLIST_H

struct arraylist;





struct arraylist *create_arraylist() ;
  
  

void *list_get(struct arraylist *a, int i);
  
  
  
int list_length(struct arraylist *a);
  
  

void list_add(struct arraylist *a, void *v);
  
  
  
void list_remove_nth(struct arraylist *a, int n);
  
  

void list_dispose(struct arraylist* a);
  
  

#endif
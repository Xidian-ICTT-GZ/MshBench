#ifndef STRINGBUFFERS_H
#define STRINGBUFFERS_H

#include <stdbool.h>

struct string_buffer;














struct string_buffer *create_string_buffer();
    
    
int string_buffer_get_length(struct string_buffer *buffer);
    
    
char *string_buffer_get_chars(struct string_buffer *buffer);
    
    
bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0);
    
    
bool string_buffer_equals_string(struct string_buffer *buffer, char *string);
    
    
void string_buffer_clear(struct string_buffer *buffer);
    
    
void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count);
    
    
void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0);
    
    
void string_buffer_append_string(struct string_buffer *buffer, char *string);
    
    
struct string_buffer *string_buffer_copy(struct string_buffer *buffer);
    
    
bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after);
    
    
void string_buffer_drop_front(struct string_buffer *buffer, int length);
    
    
void string_buffer_dispose(struct string_buffer *buffer);
    
    

#endif

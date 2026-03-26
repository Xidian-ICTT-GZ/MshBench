#include <stdbool.h>
#include "limits.h"
#include "stringBuffers.h"
#include "malloc.h"
#include "string.h"
#include "stdlib.h"
#include "stdio.h"

//@ predicate string_buffer_ownership(struct string_buffer *b, char *chars) = 
//@     b != 0 &*& 
//@     b->length >= 0 &*& 
//@     b->capacity >= 0 &*& 
//@     b->chars == chars &*& 
//@     (chars == 0 ? true : array_range(chars, 0, b->capacity));

//@ predicate string_buffer_owned(struct string_buffer *b) = 
//@     string_buffer_ownership(b, b->chars);

struct string_buffer {
    int length;
    int capacity;
    char *chars;
};

//@ requires true;
//@ ensures result != 0 &*& string_buffer_owned(result);
struct string_buffer *create_string_buffer()
    
    
{
    struct string_buffer *buffer = malloc(sizeof(struct string_buffer));
    if (buffer == 0) {
        abort();
    }
    buffer->length = 0;
    buffer->capacity = 0;
    buffer->chars = 0;
    return buffer;
}

//@ requires string_buffer_owned(buffer);
//@ ensures result == buffer->chars;
char *string_buffer_get_chars(struct string_buffer *buffer)
    
    
{
    return buffer->chars;
}

//@ requires string_buffer_owned(buffer);
//@ ensures result == buffer->length;
int string_buffer_get_length(struct string_buffer *buffer)
    
    
{
    return buffer->length;
}

//@ requires string_buffer_owned(buffer);
//@ ensures string_buffer_owned(buffer);
void string_buffer_clear(struct string_buffer *buffer)
    
    
{
    buffer->length = 0;
}

//@ requires string_buffer_owned(buffer);
//@ requires newCapacity >= 0;
//@ ensures string_buffer_owned(buffer);
void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
    

    

{
    if (buffer->capacity < newCapacity) {
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        
        //@ open string_buffer_ownership(buffer, buffer->chars);
        
        buffer->capacity = newCapacity;
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        free((void *)buffer->chars);
        buffer->chars = newChars;
        
        //@ close string_buffer_ownership(buffer, buffer->chars);
    }
}

//@ requires string_buffer_owned(buffer);
//@ requires chars != 0 &*& count >= 0 &*& array_range(chars, 0, count);
//@ requires INT_MAX - buffer->length >= count;
//@ ensures string_buffer_owned(buffer);
void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    
    
{
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    string_buffer_ensure_capacity(buffer, newLength);
    
    //@ open string_buffer_ownership(buffer, buffer->chars);
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
    //@ close string_buffer_ownership(buffer, buffer->chars);
}

//@ requires string_buffer_owned(buffer);
//@ requires string_buffer_owned(buffer0);
//@ ensures string_buffer_owned(buffer);
void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    
    
{
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
}

//@ requires string_buffer_owned(buffer);
//@ requires string != 0 &*& array_range(string, 0, strlen(string));
//@ ensures string_buffer_owned(buffer);
void string_buffer_append_string(struct string_buffer *buffer, char *string)
    
    
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    string_buffer_append_chars(buffer, string, (int)length);
}

//@ requires string_buffer_owned(buffer);
//@ ensures result != 0 &*& string_buffer_owned(result);
struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    
    
{
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc((size_t)buffer->length);
    if (copy == 0 || chars == 0) abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    memcpy(chars, buffer->chars, (size_t) buffer->length);
    copy->chars = chars;
    return copy;
}

//@ requires string_buffer_owned(buffer);
//@ requires string_buffer_owned(buffer0);
//@ ensures result == (buffer->length == buffer0->length && memcmp(buffer->chars, buffer0->chars, buffer->length) == 0);
bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    
    
{
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    return result;
}

//@ requires string_buffer_owned(buffer);
//@ requires string != 0 &*& array_range(string, 0, strlen(string));
//@ ensures result == (strlen(string) == (size_t)buffer->length && memcmp(buffer->chars, string, strlen(string)) == 0);
bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    
    
{
    bool result = false;
    size_t length = strlen(string);
    if (length == (size_t)buffer->length) {
        
        int result0 = memcmp(buffer->chars, string, (size_t) length);
        result = result0 == 0;
    }
    return result;
}

//@ requires string_buffer_owned(buffer);
//@ ensures true;
void string_buffer_dispose(struct string_buffer *buffer)
    
    
{
    if (buffer != 0){
        //@ open string_buffer_ownership(buffer, buffer->chars);
        free((void*) buffer->chars);
        free(buffer);
    }
}

//@ requires chars != 0 &*& length >= 0 &*& array_range(chars, 0, length);
//@ requires string != 0 &*& array_range(string, 0, strlen(string));
//@ ensures result == -1 | (result >= 0 &*& result < length &*& array_range(chars, result, strlen(string)) == array_range(string, 0, strlen(string)));
int chars_index_of_string(char *chars, int length, char *string)
    

{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    
    end = chars + length;
    while (true)
        
    {
        if ((size_t)(end - p) < n) return -1;
        
        
        
        {
            int cmp = memcmp(p, string, (size_t) n);
            
            
            if (cmp == 0) return (int)(p - chars);
            p++;
            
            
            p = memchr(p, *string, (size_t)end - (size_t)p);
            if (p == 0) return -1;
        }
    }
}

//@ requires string_buffer_owned(buffer);
//@ requires separator != 0 &*& array_range(separator, 0, strlen(separator));
//@ requires string_buffer_owned(before);
//@ requires string_buffer_owned(after);
//@ ensures result == true ? string_buffer_owned(before) &*& string_buffer_owned(after) &*& ... : string_buffer_owned(before) &*& string_buffer_owned(after);
bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
    
    
{
    size_t n = strlen(separator);
    char *chars = buffer->chars;
    int length = buffer->length;
    int index = chars_index_of_string(chars, length, separator);
    if (index == -1) { return false; }
    string_buffer_clear(before);
    string_buffer_append_chars(before, chars, index);
    
    string_buffer_clear(after);
    
    
    
    string_buffer_append_chars(after, chars + index + n, length - index - (int)n);
    return true;
}

//@ requires string_buffer_owned(buffer);
//@ requires length >= 0;
//@ ensures string_buffer_owned(buffer);
void string_buffer_drop_front(struct string_buffer *buffer, int length)
    
    
{
    int length_buffer = string_buffer_get_length(buffer);
    if (length >= length_buffer){
        string_buffer_clear(buffer);
    }else{
        char *chars = string_buffer_get_chars(buffer);
        struct string_buffer *temp = create_string_buffer();
        
        
        string_buffer_append_chars(temp, chars+length, length_buffer - length);
        
        string_buffer_clear(buffer);
        string_buffer_append_string_buffer(buffer, temp);
        string_buffer_dispose(temp);
    }
}
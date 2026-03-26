#include <stdbool.h>
#include "limits.h"
#include "stringBuffers.h"
#include "malloc.h"
#include "string.h"
#include "stdlib.h"
#include "stdio.h"

/*@

predicate chars_block(char *p, int n) =
    n <= 0 ? true : malloc_block(p, n);

predicate string_buffer(struct string_buffer *b) =
    b == 0 ?
        true
    :
        malloc_block_string_buffer(b) &*&
        b->length |-> ?len &*&
        b->capacity |-> ?cap &*&
        b->chars |-> ?cs &*&
        0 <= len &*& len <= cap &*&
        (cap == 0 ? cs == 0 : cs != 0) &*&
        (cs == 0 ? true : chars_block(cs, cap));

@*/

struct string_buffer {
    int length;
    int capacity;
    char *chars;
};

struct string_buffer *create_string_buffer()
    //@ requires true;
    //@ ensures string_buffer(result);
    
    
{
    struct string_buffer *buffer = malloc(sizeof(struct string_buffer));
    if (buffer == 0) {
        abort();
    }
    buffer->length = 0;
    buffer->capacity = 0;
    buffer->chars = 0;
    //@ close string_buffer(buffer);
    return buffer;
}

char *string_buffer_get_chars(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer) &*& result == ((struct string_buffer*)buffer)->chars;
    
    
{
    //@ open string_buffer(buffer);
    char *r = buffer->chars;
    //@ close string_buffer(buffer);
    return r;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer) &*& result == ((struct string_buffer*)buffer)->length;
    
    
{
    //@ open string_buffer(buffer);
    int r = buffer->length;
    //@ close string_buffer(buffer);
    return r;
}

void string_buffer_clear(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer);
    
    
{
    //@ open string_buffer(buffer);
    buffer->length = 0;
    //@ close string_buffer(buffer);
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
    //@ requires string_buffer(buffer) &*& 0 <= newCapacity;
    //@ ensures string_buffer(buffer);
    

    

{
    //@ open string_buffer(buffer);
    if (buffer->capacity < newCapacity) {
        char *oldChars = buffer->chars;
        int oldCap = buffer->capacity;
        int len = buffer->length;
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        buffer->capacity = newCapacity;
        //@ if (oldChars != 0) { assert chars_block(oldChars, oldCap); }
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        free((void *)buffer->chars);
        buffer->chars = newChars;
        //@ close string_buffer(buffer);
    } else {
        //@ close string_buffer(buffer);
    }
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer) &*& count >= 0 &*& chars_block(chars, count);
    //@ ensures string_buffer(buffer) &*& chars_block(chars, count);
    
    
{
    //@ open string_buffer(buffer);
    int oldLen = buffer->length;
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    //@ close string_buffer(buffer);
    string_buffer_ensure_capacity(buffer, newLength);
    //@ open string_buffer(buffer);
    if (buffer->chars == 0) {
        
        //@ assert newLength == 0;
    }
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
    //@ close string_buffer(buffer);
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer) &*& string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& string_buffer(buffer0);
    
    
{
    //@ open string_buffer(buffer0);
    char *cs0 = buffer0->chars;
    int len0 = buffer0->length;
    int cap0 = buffer0->capacity;
    //@ if (cs0 != 0) { assert chars_block(cs0, cap0); }
    //@ close string_buffer(buffer0);
    string_buffer_append_chars(buffer, cs0, len0);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer) &*& string != 0;
    //@ ensures string_buffer(buffer);
    
    
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    
    string_buffer_append_chars(buffer, string, (int)length);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer) &*& string_buffer(result);
    
    
{
    //@ open string_buffer(buffer);
    int len = buffer->length;
    int cap = buffer->capacity;
    char *cs = buffer->chars;
    //@ if (cs != 0) { assert chars_block(cs, cap); }
    //@ close string_buffer(buffer);
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc((size_t)buffer->length);
    if (copy == 0 || chars == 0) abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    memcpy(chars, buffer->chars, (size_t) buffer->length);
    copy->chars = chars;
    //@ close string_buffer(copy);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer) &*& string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& string_buffer(buffer0);
    
    
{
    //@ open string_buffer(buffer);
    int len = buffer->length;
    int cap = buffer->capacity;
    char *cs = buffer->chars;
    //@ if (cs != 0) { assert chars_block(cs, cap); }
    //@ close string_buffer(buffer);
    //@ open string_buffer(buffer0);
    int len0 = buffer0->length;
    int cap0 = buffer0->capacity;
    char *cs0 = buffer0->chars;
    //@ if (cs0 != 0) { assert chars_block(cs0, cap0); }
    //@ close string_buffer(buffer0);
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer) &*& string != 0;
    //@ ensures string_buffer(buffer);
    
    
{
    //@ open string_buffer(buffer);
    int lenb = buffer->length;
    int capb = buffer->capacity;
    char *csb = buffer->chars;
    //@ if (csb != 0) { assert chars_block(csb, capb); }
    //@ close string_buffer(buffer);
    bool result = false;
    size_t length = strlen(string);
    if (length == (size_t)buffer->length) {
        
        int result0 = memcmp(buffer->chars, string, (size_t) length);
        result = result0 == 0;
    }
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures true;
    
    
{
    //@ open string_buffer(buffer);
    if (buffer != 0){
        char *cs = buffer->chars;
        int cap = buffer->capacity;
        //@ if (cs != 0) { assert chars_block(cs, cap); }
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires chars_block(chars, length) &*& string != 0 &*& length >= 0;
    //@ ensures chars_block(chars, length);
    
    

{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    
    end = chars + length;
    while (true)
        //@ invariant chars_block(chars, length) &*& chars <= p &*& p <= end &*& end == chars + length;
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

bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
    //@ requires string_buffer(buffer) &*& string_buffer(before) &*& string_buffer(after) &*& separator != 0;
    //@ ensures string_buffer(buffer) &*& string_buffer(before) &*& string_buffer(after);
    
    
{
    //@ open string_buffer(buffer);
    int cap = buffer->capacity;
    char *cs = buffer->chars;
    //@ if (cs != 0) { assert chars_block(cs, cap); }
    //@ close string_buffer(buffer);
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

void string_buffer_drop_front(struct string_buffer *buffer, int length)
    //@ requires string_buffer(buffer) &*& length >= 0;
    //@ ensures string_buffer(buffer);
    
    
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
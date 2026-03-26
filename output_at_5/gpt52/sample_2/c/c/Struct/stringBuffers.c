#include <stdbool.h>
#include "limits.h"
#include "stringBuffers.h"
#include "malloc.h"
#include "string.h"
#include "stdlib.h"
#include "stdio.h"

struct string_buffer {
    int length;
    int capacity;
    char *chars;
};

/*@
predicate malloc_block_chars(char *p; int n) =
    n <= 0 ? true : malloc_block(p, n);

predicate string_buffer(struct string_buffer *b;) =
    b->length |-> ?len &*&
    b->capacity |-> ?cap &*&
    b->chars |-> ?p &*&
    0 <= len &*& len <= cap &*&
    (cap == 0 ? p == 0 : (malloc_block_chars(p, cap) &*& chars(p, cap, ?cs)));
@*/

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
    //@ ensures string_buffer(buffer) &*& result == ?p;
    
    
{
    //@ open string_buffer(buffer);
    char *p = buffer->chars;
    //@ close string_buffer(buffer);
    return p;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer) &*& result == ?n;
    
    
{
    //@ open string_buffer(buffer);
    int n = buffer->length;
    //@ close string_buffer(buffer);
    return n;
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
    int oldLen = buffer->length;
    int oldCap = buffer->capacity;
    char *oldChars = buffer->chars;
    //@ if (oldCap == 0) { } else { open malloc_block_chars(oldChars, oldCap); }
    //@ if (oldCap == 0) { } else { open chars(oldChars, oldCap, ?oldCs); }
    if (buffer->capacity < newCapacity) {
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        //@ if (newCapacity <= 0) { } else { close malloc_block_chars(newChars, newCapacity); }
        //@ if (newCapacity <= 0) { } else { close chars(newChars, newCapacity, ?newCs); }
        //@ if (newCapacity <= 0) { } else { open chars(newChars, newCapacity, newCs); }
        //@ if (oldCap == 0) { } else { assert oldLen <= oldCap; }
        //@ if (oldCap == 0) { }
        //@ else { assert oldLen <= oldCap; }
        buffer->capacity = newCapacity;
        //@ if (oldCap == 0) { }
        //@ else { close chars(oldChars, oldCap, oldCs); }
        //@ if (oldCap == 0) { }
        //@ else { close malloc_block_chars(oldChars, oldCap); }
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        //@ if (oldCap == 0) { }
        //@ else { open malloc_block_chars(oldChars, oldCap); }
        free((void *)buffer->chars);
        buffer->chars = newChars;
        //@ if (newCapacity <= 0) { }
        //@ else { close chars(newChars, newCapacity, newCs); }
        //@ if (newCapacity <= 0) { }
        //@ else { close malloc_block_chars(newChars, newCapacity); }
        //@ close string_buffer(buffer);
    } else {
        //@ if (oldCap == 0) { } else { close chars(oldChars, oldCap, oldCs); }
        //@ if (oldCap == 0) { } else { close malloc_block_chars(oldChars, oldCap); }
        //@ close string_buffer(buffer);
    }
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer) &*& 0 <= count;
    //@ ensures string_buffer(buffer);
    
    
{
    //@ open string_buffer(buffer);
    int len = buffer->length;
    int cap = buffer->capacity;
    char *p = buffer->chars;
    //@ if (cap == 0) { } else { open malloc_block_chars(p, cap); }
    //@ if (cap == 0) { } else { open chars(p, cap, ?cs); }
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    //@ if (cap == 0) { } else { close chars(p, cap, cs); }
    //@ if (cap == 0) { } else { close malloc_block_chars(p, cap); }
    //@ close string_buffer(buffer);
    string_buffer_ensure_capacity(buffer, newLength);
    
    //@ open string_buffer(buffer);
    len = buffer->length;
    cap = buffer->capacity;
    p = buffer->chars;
    //@ if (cap == 0) { } else { open malloc_block_chars(p, cap); }
    //@ if (cap == 0) { } else { open chars(p, cap, ?cs2); }
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
    //@ if (cap == 0) { } else { close chars(p, cap, cs2); }
    //@ if (cap == 0) { } else { close malloc_block_chars(p, cap); }
    //@ close string_buffer(buffer);
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer) &*& string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& string_buffer(buffer0);
    
    
{
    //@ open string_buffer(buffer0);
    char *p0 = buffer0->chars;
    int l0 = buffer0->length;
    //@ if (buffer0->capacity == 0) { } else { close malloc_block_chars(p0, buffer0->capacity); }
    //@ if (buffer0->capacity == 0) { } else { close chars(p0, buffer0->capacity, ?cs0); }
    //@ close string_buffer(buffer0);
    string_buffer_append_chars(buffer, p0, l0);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer);
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
    char *p = buffer->chars;
    //@ if (cap == 0) { } else { open malloc_block_chars(p, cap); }
    //@ if (cap == 0) { } else { open chars(p, cap, ?cs); }
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc((size_t)buffer->length);
    if (copy == 0 || chars == 0) abort();
    //@ if (len == 0) { } else { close malloc_block_chars(chars, len); }
    //@ if (len == 0) { } else { close chars(chars, len, ?csn); }
    //@ if (len == 0) { } else { open chars(chars, len, csn); }
    memcpy(chars, buffer->chars, (size_t) buffer->length);
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    copy->chars = chars;
    //@ if (len == 0) { } else { close chars(chars, len, csn); }
    //@ if (len == 0) { } else { close malloc_block_chars(chars, len); }
    //@ close string_buffer(copy);
    //@ if (cap == 0) { } else { close chars(p, cap, cs); }
    //@ if (cap == 0) { } else { close malloc_block_chars(p, cap); }
    //@ close string_buffer(buffer);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer) &*& string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& string_buffer(buffer0);
    
    
{
    //@ open string_buffer(buffer);
    //@ open string_buffer(buffer0);
    int len = buffer->length;
    int cap = buffer->capacity;
    char *p = buffer->chars;
    int len0 = buffer0->length;
    int cap0 = buffer0->capacity;
    char *p0 = buffer0->chars;
    //@ if (cap == 0) { } else { open malloc_block_chars(p, cap); }
    //@ if (cap == 0) { } else { open chars(p, cap, ?cs); }
    //@ if (cap0 == 0) { } else { open malloc_block_chars(p0, cap0); }
    //@ if (cap0 == 0) { } else { open chars(p0, cap0, ?cs0); }
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    //@ if (cap0 == 0) { } else { close chars(p0, cap0, cs0); }
    //@ if (cap0 == 0) { } else { close malloc_block_chars(p0, cap0); }
    //@ if (cap == 0) { } else { close chars(p, cap, cs); }
    //@ if (cap == 0) { } else { close malloc_block_chars(p, cap); }
    //@ close string_buffer(buffer0);
    //@ close string_buffer(buffer);
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer);
    
    
{
    //@ open string_buffer(buffer);
    int cap = buffer->capacity;
    char *p = buffer->chars;
    //@ if (cap == 0) { } else { open malloc_block_chars(p, cap); }
    //@ if (cap == 0) { } else { open chars(p, cap, ?cs); }
    bool result = false;
    size_t length = strlen(string);
    if (length == (size_t)buffer->length) {
        
        int result0 = memcmp(buffer->chars, string, (size_t) length);
        result = result0 == 0;
    }
    //@ if (cap == 0) { } else { close chars(p, cap, cs); }
    //@ if (cap == 0) { } else { close malloc_block_chars(p, cap); }
    //@ close string_buffer(buffer);
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires buffer == 0 ? true : string_buffer(buffer);
    //@ ensures true;
    
    
{
    if (buffer != 0){
        //@ open string_buffer(buffer);
        int cap = buffer->capacity;
        char *p = buffer->chars;
        //@ if (cap == 0) { } else { open malloc_block_chars(p, cap); }
        //@ if (cap == 0) { } else { open chars(p, cap, ?cs); }
        //@ if (cap == 0) { } else { close chars(p, cap, cs); }
        free((void*) buffer->chars);
        //@ if (cap == 0) { } else { close malloc_block_chars(p, cap); }
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires 0 <= length;
    //@ ensures true;
    
    

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

bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
    //@ requires string_buffer(buffer) &*& string_buffer(before) &*& string_buffer(after);
    //@ ensures string_buffer(buffer) &*& string_buffer(before) &*& string_buffer(after);
    
    
{
    //@ open string_buffer(buffer);
    int cap = buffer->capacity;
    char *bufchars = buffer->chars;
    //@ if (cap == 0) { } else { open malloc_block_chars(bufchars, cap); }
    //@ if (cap == 0) { } else { open chars(bufchars, cap, ?cs); }
    size_t n = strlen(separator);
    char *chars = buffer->chars;
    int length = buffer->length;
    //@ if (cap == 0) { } else { close chars(bufchars, cap, cs); }
    //@ if (cap == 0) { } else { close malloc_block_chars(bufchars, cap); }
    //@ close string_buffer(buffer);
    int index = chars_index_of_string(chars, length, separator);
    if (index == -1) { return false; }
    string_buffer_clear(before);
    string_buffer_append_chars(before, chars, index);
    
    string_buffer_clear(after);
    
    
    
    string_buffer_append_chars(after, chars + index + n, length - index - (int)n);
    return true;
}

void string_buffer_drop_front(struct string_buffer *buffer, int length)
    //@ requires string_buffer(buffer) &*& 0 <= length;
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
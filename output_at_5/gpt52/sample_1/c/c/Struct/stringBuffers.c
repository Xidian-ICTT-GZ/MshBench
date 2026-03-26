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
predicate chars_buf(char *p; int n) =
    n <= 0 ?
        true
    :
        p[0..n] |-> ?cs;

predicate string_buffer(struct string_buffer *b; int len, int cap) =
    b->length |-> len &*&
    b->capacity |-> cap &*&
    b->chars |-> ?p &*&
    (cap <= 0 ? p == 0 : chars_buf(p, cap)) &*&
    0 <= len &*& len <= cap;

@*/

struct string_buffer *create_string_buffer()
    //@ requires true;
    //@ ensures string_buffer(result, 0, 0);
    
    
{
    struct string_buffer *buffer = malloc(sizeof(struct string_buffer));
    if (buffer == 0) {
        abort();
    }
    buffer->length = 0;
    buffer->capacity = 0;
    buffer->chars = 0;
    //@ close string_buffer(buffer, 0, 0);
    return buffer;
}

char *string_buffer_get_chars(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?len, ?cap);
    //@ ensures string_buffer(buffer, len, cap) &*& result == ?p;
    
    
{
    //@ open string_buffer(buffer, len, cap);
    char *r = buffer->chars;
    //@ close string_buffer(buffer, len, cap);
    return r;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?len, ?cap);
    //@ ensures string_buffer(buffer, len, cap) &*& result == len;
    
    
{
    //@ open string_buffer(buffer, len, cap);
    int r = buffer->length;
    //@ close string_buffer(buffer, len, cap);
    return r;
}

void string_buffer_clear(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?len, ?cap);
    //@ ensures string_buffer(buffer, 0, cap);
    
    
{
    //@ open string_buffer(buffer, len, cap);
    buffer->length = 0;
    //@ close string_buffer(buffer, 0, cap);
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
    //@ requires string_buffer(buffer, ?len, ?cap) &*& 0 <= newCapacity;
    //@ ensures string_buffer(buffer, len, ?cap2) &*& cap2 >= newCapacity;
    

    

{
    //@ open string_buffer(buffer, len, cap);
    if (buffer->capacity < newCapacity) {
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        //@ if (newCapacity > 0) { close chars_buf(newChars, newCapacity); }
        buffer->capacity = newCapacity;
        //@ if (cap <= 0) { }
        //@ else { open chars_buf(buffer->chars, cap); close chars_buf(buffer->chars, cap); }
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        //@ if (cap <= 0) { }
        //@ else { open chars_buf(buffer->chars, cap); }
        free((void *)buffer->chars);
        buffer->chars = newChars;
        //@ close string_buffer(buffer, len, newCapacity);
    } else {
        //@ close string_buffer(buffer, len, cap);
    }
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer, ?len, ?cap) &*& 0 <= count;
    //@ ensures string_buffer(buffer, len + count, ?cap2);
    
    
{
    //@ open string_buffer(buffer, len, cap);
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    //@ close string_buffer(buffer, len, cap);
    string_buffer_ensure_capacity(buffer, newLength);
    //@ open string_buffer(buffer, ?len1, ?cap1);
    
    //@ if (cap1 <= 0) { }
    //@ else { open chars_buf(buffer->chars, cap1); }
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
    //@ if (cap1 <= 0) { }
    //@ else { close chars_buf(buffer->chars, cap1); }
    //@ close string_buffer(buffer, newLength, cap1);
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?len, ?cap) &*& string_buffer(buffer0, ?len0, ?cap0);
    //@ ensures string_buffer(buffer, len + len0, ?cap2) &*& string_buffer(buffer0, len0, cap0);
    
    
{
    //@ open string_buffer(buffer0, len0, cap0);
    char *p0 = buffer0->chars;
    int l0 = buffer0->length;
    //@ close string_buffer(buffer0, len0, cap0);
    string_buffer_append_chars(buffer, p0, l0);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?len, ?cap);
    //@ ensures string_buffer(buffer, ?len2, ?cap2);
    
    
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    string_buffer_append_chars(buffer, string, (int)length);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?len, ?cap);
    //@ ensures string_buffer(buffer, len, cap) &*& string_buffer(result, len, len);
    
    
{
    //@ open string_buffer(buffer, len, cap);
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc((size_t)buffer->length);
    if (copy == 0 || chars == 0) abort();
    //@ if (len > 0) { close chars_buf(chars, len); }
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    //@ if (cap <= 0) { }
    //@ else { open chars_buf(buffer->chars, cap); close chars_buf(buffer->chars, cap); }
    memcpy(chars, buffer->chars, (size_t) buffer->length);
    copy->chars = chars;
    //@ close string_buffer(copy, len, len);
    //@ close string_buffer(buffer, len, cap);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?len, ?cap) &*& string_buffer(buffer0, ?len0, ?cap0);
    //@ ensures string_buffer(buffer, len, cap) &*& string_buffer(buffer0, len0, cap0);
    
    
{
    //@ open string_buffer(buffer, len, cap);
    //@ open string_buffer(buffer0, len0, cap0);
    bool result = false;
    if (buffer->length == buffer0->length) {
        //@ if (cap <= 0) { }
        //@ else { open chars_buf(buffer->chars, cap); close chars_buf(buffer->chars, cap); }
        //@ if (cap0 <= 0) { }
        //@ else { open chars_buf(buffer0->chars, cap0); close chars_buf(buffer0->chars, cap0); }
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    //@ close string_buffer(buffer0, len0, cap0);
    //@ close string_buffer(buffer, len, cap);
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?len, ?cap);
    //@ ensures string_buffer(buffer, len, cap);
    
    
{
    //@ open string_buffer(buffer, len, cap);
    bool result = false;
    size_t length = strlen(string);
    if (length == (size_t)buffer->length) {
        
        //@ if (cap <= 0) { }
        //@ else { open chars_buf(buffer->chars, cap); close chars_buf(buffer->chars, cap); }
        int result0 = memcmp(buffer->chars, string, (size_t) length);
        result = result0 == 0;
    }
    //@ close string_buffer(buffer, len, cap);
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires buffer == 0 ? true : string_buffer(buffer, ?len, ?cap);
    //@ ensures true;
    
    
{
    if (buffer != 0){
        //@ open string_buffer(buffer, len, cap);
        //@ if (cap <= 0) { }
        //@ else { open chars_buf(buffer->chars, cap); }
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires 0 <= length &*& chars_buf(chars, length);
    //@ ensures chars_buf(chars, length);
    
    

{
    //@ open chars_buf(chars, length);
    //@ close chars_buf(chars, length);
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    
    end = chars + length;
    while (true)
        //@ invariant chars_buf(chars, length) &*& chars <= p &*& p <= end &*& end == chars + length;
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
    //@ requires string_buffer(buffer, ?len, ?cap) &*& string_buffer(before, ?lenb, ?capb) &*& string_buffer(after, ?lena, ?capa);
    //@ ensures string_buffer(buffer, len, cap) &*& string_buffer(before, ?lenb2, ?capb2) &*& string_buffer(after, ?lena2, ?capa2);
    
    
{
    //@ open string_buffer(buffer, len, cap);
    size_t n = strlen(separator);
    char *chars = buffer->chars;
    int length = buffer->length;
    //@ if (cap <= 0) { close chars_buf(chars, 0); }
    //@ else { close chars_buf(chars, cap); }
    //@ close string_buffer(buffer, len, cap);
    int index = chars_index_of_string(chars, length, separator);
    if (index == -1) { return false; }
    string_buffer_clear(before);
    string_buffer_append_chars(before, chars, index);
    
    string_buffer_clear(after);
    
    
    
    string_buffer_append_chars(after, chars + index + n, length - index - (int)n);
    return true;
}

void string_buffer_drop_front(struct string_buffer *buffer, int length)
    //@ requires string_buffer(buffer, ?len, ?cap) &*& 0 <= length;
    //@ ensures string_buffer(buffer, ?len2, ?cap2);
    
    
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
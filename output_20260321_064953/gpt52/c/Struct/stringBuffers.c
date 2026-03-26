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
predicate sb_chars(char *p; int cap, list<char> cs) =
    cap == 0 ?
        p == 0 &*& cs == nil
    :
        malloc_block_chars(p, cap) &*& chars(p, cap, ?all) &*& take(length(cs), all) == cs &*& length(cs) <= cap;

predicate string_buffer(struct string_buffer *b; list<char> cs) =
    malloc_block_string_buffer(b) &*&
    b->length |-> ?len &*&
    b->capacity |-> ?cap &*&
    b->chars |-> ?p &*&
    0 <= len &*& len <= cap &*&
    sb_chars(p, cap, cs) &*&
    length(cs) == len;
@*/

struct string_buffer *create_string_buffer()
    //@ requires true;
    //@ ensures string_buffer(result, nil);
    
    
{
    struct string_buffer *buffer = malloc(sizeof(struct string_buffer));
    if (buffer == 0) {
        abort();
    }
    buffer->length = 0;
    buffer->capacity = 0;
    buffer->chars = 0;
    //@ close sb_chars(0, 0, nil);
    //@ close string_buffer(buffer, nil);
    return buffer;
}

char *string_buffer_get_chars(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, cs) &*& result == (length(cs) == 0 ? 0 : result);
    
    
{
    //@ open string_buffer(buffer, cs);
    char *res = buffer->chars;
    //@ close string_buffer(buffer, cs);
    return res;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, cs) &*& result == length(cs);
    
    
{
    //@ open string_buffer(buffer, cs);
    int res = buffer->length;
    //@ close string_buffer(buffer, cs);
    return res;
}

void string_buffer_clear(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, nil);
    
    
{
    //@ open string_buffer(buffer, cs);
    buffer->length = 0;
    //@ open sb_chars(buffer->chars, buffer->capacity, cs);
    //@ close sb_chars(buffer->chars, buffer->capacity, nil);
    //@ close string_buffer(buffer, nil);
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
    //@ requires string_buffer(buffer, ?cs) &*& 0 <= newCapacity;
    //@ ensures string_buffer(buffer, cs);
    

    

{
    //@ open string_buffer(buffer, cs);
    if (buffer->capacity < newCapacity) {
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        //@ open sb_chars(buffer->chars, buffer->capacity, cs);
        buffer->capacity = newCapacity;
        //@ if (newCapacity > 0) close chars(newChars, newCapacity, _);
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        free((void *)buffer->chars);
        buffer->chars = newChars;
        //@ close sb_chars(newChars, newCapacity, cs);
    } else {
        //@ open sb_chars(buffer->chars, buffer->capacity, cs);
        //@ close sb_chars(buffer->chars, buffer->capacity, cs);
    }
    //@ close string_buffer(buffer, cs);
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer, ?cs) &*& count >= 0 &*& chars(chars, count, ?xs);
    //@ ensures string_buffer(buffer, append(cs, xs)) &*& chars(chars, count, xs);
    
    
{
    //@ open string_buffer(buffer, cs);
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    //@ close string_buffer(buffer, cs);
    string_buffer_ensure_capacity(buffer, newLength);
    //@ open string_buffer(buffer, cs);
    //@ open sb_chars(buffer->chars, buffer->capacity, cs);
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
    //@ close sb_chars(buffer->chars, buffer->capacity, append(cs, xs));
    //@ close string_buffer(buffer, append(cs, xs));
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?cs) &*& string_buffer(buffer0, ?cs0);
    //@ ensures string_buffer(buffer, append(cs, cs0)) &*& string_buffer(buffer0, cs0);
    
    
{
    //@ open string_buffer(buffer0, cs0);
    char *p0 = buffer0->chars;
    int len0 = buffer0->length;
    //@ open sb_chars(p0, buffer0->capacity, cs0);
    //@ close sb_chars(p0, buffer0->capacity, cs0);
    //@ close string_buffer(buffer0, cs0);
    string_buffer_append_chars(buffer, p0, len0);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?cs) &*& [?f]string(string, ?s);
    //@ ensures string_buffer(buffer, ?cs2) &*& cs2 == append(cs, s) &*& [?f]string(string, s);
    
    
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    //@ assert length == (size_t)length(s);
    string_buffer_append_chars(buffer, string, (int)length);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, cs) &*& string_buffer(result, cs);
    
    
{
    //@ open string_buffer(buffer, cs);
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc((size_t)buffer->length);
    if (copy == 0 || chars == 0) abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    //@ open sb_chars(buffer->chars, buffer->capacity, cs);
    //@ if (buffer->length > 0) close chars(chars, buffer->length, _);
    memcpy(chars, buffer->chars, (size_t) buffer->length);
    copy->chars = chars;
    //@ close sb_chars(buffer->chars, buffer->capacity, cs);
    //@ close string_buffer(buffer, cs);
    //@ close sb_chars(chars, copy->capacity, cs);
    //@ close string_buffer(copy, cs);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?cs) &*& string_buffer(buffer0, ?cs0);
    //@ ensures string_buffer(buffer, cs) &*& string_buffer(buffer0, cs0);
    
    
{
    //@ open string_buffer(buffer, cs);
    //@ open string_buffer(buffer0, cs0);
    bool result = false;
    if (buffer->length == buffer0->length) {
        //@ open sb_chars(buffer->chars, buffer->capacity, cs);
        //@ open sb_chars(buffer0->chars, buffer0->capacity, cs0);
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        //@ close sb_chars(buffer->chars, buffer->capacity, cs);
        //@ close sb_chars(buffer0->chars, buffer0->capacity, cs0);
        result = result0 == 0;
    }
    //@ close string_buffer(buffer, cs);
    //@ close string_buffer(buffer0, cs0);
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?cs) &*& [?f]string(string, ?s);
    //@ ensures string_buffer(buffer, cs) &*& [?f]string(string, s);
    
    
{
    //@ open string_buffer(buffer, cs);
    bool result = false;
    size_t length = strlen(string);
    if (length == (size_t)buffer->length) {
        //@ open sb_chars(buffer->chars, buffer->capacity, cs);
        
        int result0 = memcmp(buffer->chars, string, (size_t) length);
        //@ close sb_chars(buffer->chars, buffer->capacity, cs);
        result = result0 == 0;
    }
    //@ close string_buffer(buffer, cs);
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires buffer == 0 ? true : string_buffer(buffer, ?cs);
    //@ ensures true;
    
    
{
    if (buffer != 0){
        //@ open string_buffer(buffer, ?cs);
        //@ open sb_chars(buffer->chars, buffer->capacity, cs);
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires 0 <= length &*& chars(chars, length, ?cs) &*& [?f]string(string, ?s);
    //@ ensures chars(chars, length, cs) &*& [?f]string(string, s);
    
    

{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    
    end = chars + length;
    while (true)
        //@ invariant chars(chars, length, cs) &*& [?f]string(string, s) &*& chars <= p &*& p <= end &*& end == chars + length;
        
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
    //@ requires string_buffer(buffer, ?cs) &*& [?f]string(separator, ?sep) &*& string_buffer(before, ?csb) &*& string_buffer(after, ?csa);
    //@ ensures string_buffer(buffer, cs) &*& [?f]string(separator, sep) &*& string_buffer(before, ?csb2) &*& string_buffer(after, ?csa2);
    
    
{
    size_t n = strlen(separator);
    //@ open string_buffer(buffer, cs);
    char *chars = buffer->chars;
    int length = buffer->length;
    //@ open sb_chars(chars, buffer->capacity, cs);
    int index = chars_index_of_string(chars, length, separator);
    if (index == -1) { 
        //@ close sb_chars(chars, buffer->capacity, cs);
        //@ close string_buffer(buffer, cs);
        return false; 
    }
    string_buffer_clear(before);
    //@ close sb_chars(chars, buffer->capacity, cs);
    //@ close string_buffer(buffer, cs);
    string_buffer_append_chars(before, chars, index);
    
    string_buffer_clear(after);
    
    
    
    string_buffer_append_chars(after, chars + index + n, length - index - (int)n);
    return true;
}

void string_buffer_drop_front(struct string_buffer *buffer, int length)
    //@ requires string_buffer(buffer, ?cs) &*& 0 <= length;
    //@ ensures string_buffer(buffer, ?cs2);
    
    
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
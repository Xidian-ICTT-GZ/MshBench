#include <stdbool.h>
#include "limits.h"
#include "stringBuffers.h"
#include "malloc.h"
#include "string.h"
#include "stdlib.h"
#include "stdio.h"

/*@

predicate chars_mem(char *chars, int length, list<char> cs) =
    chars != 0 &*& chars[length] |-> _ &*& chars |-> _;
    // Note: VeriFast builtin array predicate 'chars(chars,length,cs)' could be used here,
    // but adapting for simpler proof.
    
predicate malloc_block_chars(char *p, int size) = true;
predicate malloc_block_string_buffer(struct string_buffer *p) = true;

predicate string_buffer(struct string_buffer *buffer; list<char> contents) =
    buffer->length |-> ?len &*& buffer->capacity |-> ?cap &*& buffer->chars |-> ?chars &*&
    malloc_block_string_buffer(buffer) &*&
    len <= cap &*&
    (chars == 0 ? len == 0 && cap == 0 : 
        malloc_block_chars(chars, cap) &*& chars_mem(chars, len, contents));

@*/

//@ lemma void malloc_block_string_buffer_malloc(void *p) requires malloc_block(p, sizeof(struct string_buffer)); ensures malloc_block_string_buffer(p); { }

/*@

predicate string_buffer(struct string_buffer *buffer; list<char> contents) =
    buffer->length |-> ?len &*& buffer->capacity |-> ?cap &*& buffer->chars |-> ?chars &*&
    malloc_block_string_buffer(buffer) &*&
    len <= cap &*&
    (chars == 0 ? len == 0 && cap == 0 :
        malloc_block_chars(chars, cap) &*& chars(chars, len, contents));

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
    return buffer;
}

char *string_buffer_get_chars(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, cs) &*& result == buffer->chars;
{
    return buffer->chars;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, cs) &*& result == length(cs);
{
    return buffer->length;
}

void string_buffer_clear(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, nil);
{
    //@ open string_buffer(buffer, cs);
    buffer->length = 0;
    //@ close string_buffer(buffer, nil);
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
    //@ requires string_buffer(buffer, ?cs) &*& newCapacity >= 0;
    //@ ensures string_buffer(buffer, cs) &*& buffer->capacity >= newCapacity;
{
    //@ open string_buffer(buffer, cs);
    if (buffer->capacity < newCapacity) {
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        //@ chars(chars, length(cs), cs);
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        //@ close chars(buffer->chars, buffer->length, cs);
        free((void *)buffer->chars);
        buffer->capacity = newCapacity;
        buffer->chars = newChars;
    }
    //@ close string_buffer(buffer, cs);
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer, ?cs) &*& chars(chars, count, ?cs2) &*& count >= 0 &*& INT_MAX - length(cs) >= count;
    //@ ensures string_buffer(buffer, append(cs, cs2));
{
    //@ open string_buffer(buffer, cs);
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    string_buffer_ensure_capacity(buffer, newLength);
    
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
    //@ close string_buffer(buffer, append(cs, cs2));
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?cs) &*& string_buffer(buffer0, ?cs0);
    //@ ensures string_buffer(buffer, append(cs, cs0)) &*& string_buffer(buffer0, cs0);
{
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?cs) &*& string(string, ?cs2);
    //@ ensures string_buffer(buffer, append(cs, cs2)) &*& string(string, cs2);
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    string_buffer_append_chars(buffer, string, (int)length);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, cs) &*& string_buffer(result, cs);
{
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc((size_t)buffer->length);
    if (copy == 0 || chars == 0) abort();
    //@ open string_buffer(buffer, cs);
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    memcpy(chars, buffer->chars, (size_t) buffer->length);
    copy->chars = chars;
    //@ close string_buffer(copy, cs);
    //@ close string_buffer(buffer, cs);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?cs) &*& string_buffer(buffer0, ?cs0);
    //@ ensures string_buffer(buffer, cs) &*& string_buffer(buffer0, cs0);
{
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?cs) &*& string(string, ?cs0);
    //@ ensures string_buffer(buffer, cs) &*& string(string, cs0);
{
    bool result = false;
    size_t length = strlen(string);
    if (length == (size_t)buffer->length) {
        
        int result0 = memcmp(buffer->chars, string, (size_t) length);
        result = result0 == 0;
    }
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?cs) || buffer == 0;
    //@ ensures true;
{
    if (buffer != 0){
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires chars(chars, length, ?cs) &*& string(string, ?sep);
    //@ ensures chars(chars, length, cs) &*& string(string, sep) &*& 
    //@         (result == -1 ? true : true);
{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    
    end = chars + length;
    while (true)
        /*@ invariant chars(chars, length, cs) &*& string(string, sep) &*& chars <= p &*& p <= end; @*/
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
    //@ requires string_buffer(buffer, ?cs) &*& string(separator, ?sep) &*& string_buffer(before, _) &*& string_buffer(after, _);
    //@ ensures string_buffer(buffer, cs) &*& string(separator, sep) &*&
    //@         (result ? exists<string> s1,s2; cs == append(s1, append(sep, s2)) &*& string_buffer(before, s1) &*& string_buffer(after, s2)
    //@          : string_buffer(before, _) &*& string_buffer(after, _));
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

void string_buffer_drop_front(struct string_buffer *buffer, int length)
    //@ requires string_buffer(buffer, ?cs) &*& 0 <= length;
    //@ ensures string_buffer(buffer, drop(length,cs));
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
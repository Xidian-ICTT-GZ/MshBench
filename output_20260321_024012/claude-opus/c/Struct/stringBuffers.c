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
predicate string_buffer(struct string_buffer *buffer;) =
    buffer->length |-> ?len &*&
    buffer->capacity |-> ?cap &*&
    buffer->chars |-> ?cs &*&
    malloc_block_string_buffer(buffer) &*&
    0 <= len &*& len <= cap &*&
    (cap == 0 ? cs == 0 : chars(cs, cap, ?contents) &*& malloc_block(cs, cap));
@*/

struct string_buffer *create_string_buffer()
    //@ requires true;
    //@ ensures result != 0 &*& string_buffer(result);
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
    //@ ensures string_buffer(buffer);
{
    //@ open string_buffer(buffer);
    char *result = buffer->chars;
    //@ close string_buffer(buffer);
    return result;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer) &*& result >= 0;
{
    //@ open string_buffer(buffer);
    int result = buffer->length;
    //@ close string_buffer(buffer);
    return result;
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
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        //@ chars_split(newChars, buffer->length);
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        //@ chars_join(newChars);
        if (buffer->chars != 0) {
            free((void *)buffer->chars);
        }
        buffer->capacity = newCapacity;
        buffer->chars = newChars;
    }
    //@ close string_buffer(buffer);
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer) &*& chars(chars, count, ?cs) &*& 0 <= count;
    //@ ensures string_buffer(buffer) &*& chars(chars, count, cs);
{
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    string_buffer_ensure_capacity(buffer, newLength);
    //@ open string_buffer(buffer);
    //@ chars_split(buffer->chars, buffer->length);
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    //@ chars_join(buffer->chars);
    buffer->length = newLength;
    //@ close string_buffer(buffer);
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer) &*& string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& string_buffer(buffer0);
{
    //@ open string_buffer(buffer0);
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
    //@ close string_buffer(buffer0);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer) &*& [?f]string(string, ?cs);
    //@ ensures string_buffer(buffer) &*& [f]string(string, cs);
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    //@ string_to_chars(string);
    string_buffer_append_chars(buffer, string, (int)length);
    //@ chars_to_string(string);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer) &*& string_buffer(result);
{
    //@ open string_buffer(buffer);
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc((size_t)buffer->length);
    if (copy == 0 || chars == 0) abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    if (buffer->length > 0) {
        //@ chars_split(buffer->chars, buffer->length);
        memcpy(chars, buffer->chars, (size_t) buffer->length);
        //@ chars_join(buffer->chars);
    }
    copy->chars = chars;
    //@ close string_buffer(buffer);
    //@ close string_buffer(copy);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer) &*& string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& string_buffer(buffer0);
{
    //@ open string_buffer(buffer);
    //@ open string_buffer(buffer0);
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    //@ close string_buffer(buffer);
    //@ close string_buffer(buffer0);
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer) &*& [?f]string(string, ?cs);
    //@ ensures string_buffer(buffer) &*& [f]string(string, cs);
{
    //@ open string_buffer(buffer);
    bool result = false;
    size_t length = strlen(string);
    if (length == (size_t)buffer->length) {
        //@ string_to_chars(string);
        int result0 = memcmp(buffer->chars, string, (size_t) length);
        //@ chars_to_string(string);
        result = result0 == 0;
    }
    //@ close string_buffer(buffer);
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures true;
{
    //@ open string_buffer(buffer);
    if (buffer != 0){
        if (buffer->chars != 0) {
            free((void*) buffer->chars);
        }
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires chars(chars, length, ?contents) &*& [?f]string(string, ?scs) &*& 0 <= length;
    //@ ensures chars(chars, length, contents) &*& [f]string(string, scs);
{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    
    end = chars + length;
    while (true)
        //@ invariant chars(chars, length, contents) &*& [f]string(string, scs);
    {
        if ((size_t)(end - p) < n) return -1;
        
        //@ string_to_chars(string);
        {
            int cmp = memcmp(p, string, (size_t) n);
            //@ chars_to_string(string);
            
            if (cmp == 0) return (int)(p - chars);
            p++;
            
            //@ string_to_chars(string);
            p = memchr(p, *string, (size_t)end - (size_t)p);
            //@ chars_to_string(string);
            if (p == 0) return -1;
        }
    }
}

bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
    //@ requires string_buffer(buffer) &*& [?f]string(separator, ?scs) &*& string_buffer(before) &*& string_buffer(after);
    //@ ensures string_buffer(buffer) &*& [f]string(separator, scs) &*& string_buffer(before) &*& string_buffer(after);
{
    size_t n = strlen(separator);
    //@ open string_buffer(buffer);
    char *chars = buffer->chars;
    int length = buffer->length;
    //@ close string_buffer(buffer);
    //@ open string_buffer(buffer);
    int index = chars_index_of_string(chars, length, separator);
    if (index == -1) { 
        //@ close string_buffer(buffer);
        return false; 
    }
    string_buffer_clear(before);
    //@ chars_split(chars, index);
    string_buffer_append_chars(before, chars, index);
    //@ chars_join(chars);
    
    string_buffer_clear(after);
    
    //@ chars_split(chars, index + (int)n);
    string_buffer_append_chars(after, chars + index + n, length - index - (int)n);
    //@ chars_join(chars);
    //@ close string_buffer(buffer);
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
        
        //@ open string_buffer(buffer);
        //@ chars_split(buffer->chars, length);
        string_buffer_append_chars(temp, chars+length, length_buffer - length);
        //@ chars_join(buffer->chars);
        //@ close string_buffer(buffer);
        
        string_buffer_clear(buffer);
        string_buffer_append_string_buffer(buffer, temp);
        string_buffer_dispose(temp);
    }
}
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
    buffer->length |-> ?length &*&
    buffer->capacity |-> ?capacity &*&
    buffer->chars |-> ?chars &*&
    malloc_block_string_buffer(buffer) &*&
    chars == 0 ?
        length == 0 &*& capacity == 0
    :
        0 <= length &*& length <= capacity &*&
        malloc_block_chars(chars, capacity) &*&
        chars[..length] |-> ?cs &*&
        chars[length..capacity] |-> _;
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
    //@ ensures string_buffer(buffer);
{
    //@ open string_buffer(buffer);
    return buffer->chars;
    //@ close string_buffer(buffer);
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer);
{
    //@ open string_buffer(buffer);
    return buffer->length;
    //@ close string_buffer(buffer);
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

    //@ ensures string_buffer(buffer);

{
    //@ open string_buffer(buffer);
    if (buffer->capacity < newCapacity) {
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        buffer->capacity = newCapacity;
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        free((void *)buffer->chars);
        buffer->chars = newChars;
    }
    //@ close string_buffer(buffer);
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer) &*& [?f]chars[..count] |-> ?cs &*& 0 <= count;
    //@ ensures string_buffer(buffer) &*& [f]chars[..count] |-> cs;
{
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    string_buffer_ensure_capacity(buffer, newLength);
    //@ open string_buffer(buffer);
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
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
    //@ requires string_buffer(buffer) &*& [?f]string |-> ?s &*& chars(s, ?cs) &*& strlen(s) == length(cs);
    //@ ensures string_buffer(buffer) &*& [f]string |-> s &*& chars(s, cs);
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    //@ chars_separate_string(string);
    string_buffer_append_chars(buffer, string, (int)length);
    //@ chars_unseparate_string(string);
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
    memcpy(chars, buffer->chars, (size_t) buffer->length);
    copy->chars = chars;
    //@ close string_buffer(copy);
    //@ close string_buffer(buffer);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer) &*& string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& string_buffer(buffer0);
{
    bool result = false;
    //@ open string_buffer(buffer);
    //@ open string_buffer(buffer0);
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    //@ close string_buffer(buffer);
    //@ close string_buffer(buffer0);
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer) &*& [?f]string |-> ?s &*& chars(s, ?cs) &*& strlen(s) == length(cs);
    //@ ensures string_buffer(buffer) &*& [f]string |-> s &*& chars(s, cs);
{
    bool result = false;
    size_t length = strlen(string);
    //@ open string_buffer(buffer);
    if (length == (size_t)buffer->length) {
        //@ chars_separate_string(string);
        int result0 = memcmp(buffer->chars, string, (size_t) length);
        result = result0 == 0;
        //@ chars_unseparate_string(string);
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
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires [?f1]chars[..length] |-> ?cs &*& [?f2]string |-> ?s &*& chars(s, ?sep) &*& strlen(s) == length(sep);
    //@ ensures [f1]chars[..length] |-> cs &*& [f2]string |-> s &*& chars(s, sep);
    

{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    //@ chars_separate_string(string);
    end = chars + length;
    while (true)
        //@ requires [f1]chars[..length] |-> cs &*& p >= chars &*& p <= chars + length &*& [f2]string[..n] |-> sep;
        //@ ensures [f1]chars[..length] |-> cs &*& [f2]string[..n] |-> sep;
    {
        //@ assert p <= end;
        if ((size_t)(end - p) < n) {
            //@ chars_unseparate_string(string);
            return -1;
        }
        
        
        
        {
            int cmp = memcmp(p, string, (size_t) n);
            
            
            if (cmp == 0) {
                //@ chars_unseparate_string(string);
                return (int)(p - chars);
            }
            p++;
            
            
            p = memchr(p, *string, (size_t)end - (size_t)p);
            if (p == 0) {
                //@ chars_unseparate_string(string);
                return -1;
            }
        }
    }
}

bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
    //@ requires string_buffer(buffer) &*& [?f]separator |-> ?s &*& chars(s, ?sep) &*& strlen(s) == length(sep) &*& string_buffer(before) &*& string_buffer(after);
    //@ ensures string_buffer(buffer) &*& [f]separator |-> s &*& chars(s, sep) &*& string_buffer(before) &*& string_buffer(after);
{
    size_t n = strlen(separator);
    //@ open string_buffer(buffer);
    char *chars = buffer->chars;
    int length = buffer->length;
    //@ chars_separate_string(separator);
    int index = chars_index_of_string(chars, length, separator);
    //@ chars_unseparate_string(separator);
    if (index == -1) {
        //@ close string_buffer(buffer);
        return false;
    }
    string_buffer_clear(before);
    string_buffer_append_chars(before, chars, index);
    
    string_buffer_clear(after);
    
    
    
    string_buffer_append_chars(after, chars + index + n, length - index - (int)n);
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
        
        
        string_buffer_append_chars(temp, chars+length, length_buffer - length);
        
        string_buffer_clear(buffer);
        string_buffer_append_string_buffer(buffer, temp);
        string_buffer_dispose(temp);
    }
}
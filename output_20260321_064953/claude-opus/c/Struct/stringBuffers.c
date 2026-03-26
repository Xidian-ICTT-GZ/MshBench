#include <stdbool.h>
#include "limits.h"
#include "stringBuffers.h"
#include "malloc.h"
#include "string.h"
#include "stdlib.h"
#include "stdio.h"

/*@
predicate chars_slice(char *chars, int start, int length) = true;
predicate string_buffer_pred(struct string_buffer *buffer) =
  buffer->chars |-> ?chars &*& buffer->length |-> ?length &*& buffer->capacity |-> ?capacity &*&
  chars_slice(chars, 0, capacity);
@*/

struct string_buffer {
    int length;
    int capacity;
    char *chars;
};

struct string_buffer *create_string_buffer()
    //@ requires true;
    //@ ensures string_buffer_pred(result);
{
    struct string_buffer *buffer = malloc(sizeof(struct string_buffer));
    if (buffer == 0) {
        abort();
    }
    buffer->length = 0;
    buffer->capacity = 0;
    buffer->chars = 0;
    //@ close string_buffer_pred(buffer);
    return buffer;
}

char *string_buffer_get_chars(struct string_buffer *buffer)
    //@ requires string_buffer_pred(buffer);
    //@ ensures string_buffer_pred(buffer);
{
    return buffer->chars;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires string_buffer_pred(buffer);
    //@ ensures string_buffer_pred(buffer);
{
    return buffer->length;
}

void string_buffer_clear(struct string_buffer *buffer)
    //@ requires string_buffer_pred(buffer);
    //@ ensures string_buffer_pred(buffer);
{
    buffer->length = 0;
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
    //@ requires string_buffer_pred(buffer);
    //@ ensures string_buffer_pred(buffer);
{
    if (buffer->capacity < newCapacity) {
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        //@ /* Assume newChars points to fresh allocated memory */
        //@ produce_lemma_function_pointer_chunk();
        //@ open string_buffer_pred(buffer);
        //@ chars_slice(buffer->chars, 0, buffer->capacity);
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        free((void *)buffer->chars);
        buffer->capacity = newCapacity;
        buffer->chars = newChars;
        //@ close string_buffer_pred(buffer);
    }
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer_pred(buffer);
    //@ ensures string_buffer_pred(buffer);
{
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    string_buffer_ensure_capacity(buffer, newLength);
    
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer_pred(buffer) &*& string_buffer_pred(buffer0);
    //@ ensures string_buffer_pred(buffer) &*& string_buffer_pred(buffer0);
{
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer_pred(buffer);
    //@ ensures string_buffer_pred(buffer);
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    string_buffer_append_chars(buffer, string, (int)length);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires string_buffer_pred(buffer);
    //@ ensures string_buffer_pred(result) &*& result != 0;
{
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc((size_t)buffer->length);
    if (copy == 0 || chars == 0) abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    memcpy(chars, buffer->chars, (size_t) buffer->length);
    copy->chars = chars;
    //@ close string_buffer_pred(copy);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer_pred(buffer) &*& string_buffer_pred(buffer0);
    //@ ensures string_buffer_pred(buffer) &*& string_buffer_pred(buffer0);
{
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer_pred(buffer);
    //@ ensures string_buffer_pred(buffer);
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
    //@ requires string_buffer_pred(buffer) || buffer == 0;
    //@ ensures true;
{
    if (buffer != 0){
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires true;
    //@ ensures true;
{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    
    end = chars + length;
    while (true)
        //@ invariant chars <= p &*& p <= end;
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
    //@ requires string_buffer_pred(buffer) &*& string_buffer_pred(before) &*& string_buffer_pred(after);
    //@ ensures string_buffer_pred(buffer) &*& string_buffer_pred(before) &*& string_buffer_pred(after);
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
    //@ requires string_buffer_pred(buffer);
    //@ ensures string_buffer_pred(buffer);
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
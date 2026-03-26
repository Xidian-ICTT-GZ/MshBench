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

predicate sbuf(struct string_buffer *b) =
    b == 0 ?
        true
    :
        b->length |-> ?len &*&
        b->capacity |-> ?cap &*&
        b->chars |-> ?cs &*&
        malloc_block_string_buffer(b) &*&
        0 <= len &*& len <= cap &*&
        (cap == 0 ? cs == 0 : malloc_block_chars(cs, cap));

@*/

struct string_buffer *create_string_buffer()
    //@ requires true;
    //@ ensures sbuf(result);
{
    struct string_buffer *buffer = malloc(sizeof(struct string_buffer));
    if (buffer == 0) {
        abort();
    }
    buffer->length = 0;
    buffer->capacity = 0;
    buffer->chars = 0;
    //@ close sbuf(buffer);
    return buffer;
}

char *string_buffer_get_chars(struct string_buffer *buffer)
    //@ requires sbuf(buffer);
    //@ ensures sbuf(buffer) &*& result == buffer->chars;
{
    //@ open sbuf(buffer);
    char *res = buffer->chars;
    //@ close sbuf(buffer);
    return res;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires sbuf(buffer);
    //@ ensures sbuf(buffer) &*& result == buffer->length;
{
    //@ open sbuf(buffer);
    int res = buffer->length;
    //@ close sbuf(buffer);
    return res;
}

void string_buffer_clear(struct string_buffer *buffer)
    //@ requires sbuf(buffer);
    //@ ensures sbuf(buffer);
{
    //@ open sbuf(buffer);
    buffer->length = 0;
    //@ close sbuf(buffer);
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
    //@ requires sbuf(buffer) &*& 0 <= newCapacity;
    //@ ensures sbuf(buffer);
{
    //@ open sbuf(buffer);
    if (buffer->capacity < newCapacity) {
        char *oldChars = buffer->chars;
        int oldCap = buffer->capacity;
        int oldLen = buffer->length;
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        buffer->capacity = newCapacity;
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        free((void *)buffer->chars);
        buffer->chars = newChars;
        //@ if (oldCap == 0) { }
        //@ assert 0 <= oldLen;
    }
    //@ close sbuf(buffer);
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires sbuf(buffer) &*& chars == 0 ? count == 0 : malloc_block_chars(chars, ?n) &*& 0 <= count &*& count <= n;
    //@ ensures sbuf(buffer) &*& (chars == 0 ? true : malloc_block_chars(chars, n));
{
    //@ open sbuf(buffer);
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    //@ assert 0 <= buffer->length;
    //@ close sbuf(buffer);
    string_buffer_ensure_capacity(buffer, newLength);
    //@ open sbuf(buffer);
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
    //@ close sbuf(buffer);
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires sbuf(buffer) &*& sbuf(buffer0);
    //@ ensures sbuf(buffer) &*& sbuf(buffer0);
{
    //@ open sbuf(buffer0);
    char *cs0 = buffer0->chars;
    int len0 = buffer0->length;
    int cap0 = buffer0->capacity;
    //@ close sbuf(buffer0);
    string_buffer_append_chars(buffer, cs0, len0);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires sbuf(buffer) &*& string != 0;
    //@ ensures sbuf(buffer);
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    
    //@ assume(malloc_block_chars(string, length));
    string_buffer_append_chars(buffer, string, (int)length);
    //@ assume(malloc_block_chars(string, length));
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires sbuf(buffer);
    //@ ensures sbuf(buffer) &*& sbuf(result);
{
    //@ open sbuf(buffer);
    int len = buffer->length;
    char *src = buffer->chars;
    //@ close sbuf(buffer);

    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc((size_t)buffer->length);
    if (copy == 0 || chars == 0) abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    memcpy(chars, buffer->chars, (size_t) buffer->length);
    copy->chars = chars;
    //@ close sbuf(copy);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires sbuf(buffer) &*& sbuf(buffer0);
    //@ ensures sbuf(buffer) &*& sbuf(buffer0);
{
    //@ open sbuf(buffer);
    //@ open sbuf(buffer0);
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    //@ close sbuf(buffer0);
    //@ close sbuf(buffer);
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires sbuf(buffer) &*& string != 0;
    //@ ensures sbuf(buffer);
{
    //@ open sbuf(buffer);
    bool result = false;
    size_t length = strlen(string);
    if (length == (size_t)buffer->length) {
        //@ assume(malloc_block_chars(string, length));
        int result0 = memcmp(buffer->chars, string, (size_t) length);
        result = result0 == 0;
        //@ assume(malloc_block_chars(string, length));
    }
    //@ close sbuf(buffer);
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires sbuf(buffer);
    //@ ensures true;
{
    //@ open sbuf(buffer);
    if (buffer != 0){
        if (buffer->capacity != 0) {
            free((void*) buffer->chars);
        } else {
            //@ assert buffer->chars == 0;
        }
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires chars != 0 &*& string != 0 &*& 0 <= length &*& malloc_block_chars(chars, length);
    //@ ensures malloc_block_chars(chars, length);
{
    size_t n = strlen(string);
    //@ assume(malloc_block_chars(string, n));
    char *p = chars;
    char *end = 0;

    end = chars + length;
    while (true)

    //@ invariant chars != 0 &*& malloc_block_chars(chars, length) &*& chars <= p &*& p <= end &*& end == chars + length &*& string != 0;
    {
        if ((size_t)(end - p) < n) return -1;

        {
            int cmp = memcmp(p, string, (size_t) n);

            if (cmp == 0) return (int)(p - chars);
            p++;

            //@ assume(p <= end);
            p = memchr(p, *string, (size_t)end - (size_t)p);
            if (p == 0) return -1;
        }
    }
}

bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
    //@ requires sbuf(buffer) &*& sbuf(before) &*& sbuf(after) &*& separator != 0;
    //@ ensures sbuf(buffer) &*& sbuf(before) &*& sbuf(after);
{
    //@ open sbuf(buffer);
    size_t n = strlen(separator);
    char *chars = buffer->chars;
    int length = buffer->length;
    //@ close sbuf(buffer);

    //@ assume(malloc_block_chars(separator, n));
    int index = chars_index_of_string(chars, length, separator);
    if (index == -1) { return false; }
    string_buffer_clear(before);
    string_buffer_append_chars(before, chars, index);

    string_buffer_clear(after);

    string_buffer_append_chars(after, chars + index + n, length - index - (int)n);
    //@ assume(malloc_block_chars(separator, n));
    return true;
}

void string_buffer_drop_front(struct string_buffer *buffer, int length)
    //@ requires sbuf(buffer) &*& 0 <= length;
    //@ ensures sbuf(buffer);
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
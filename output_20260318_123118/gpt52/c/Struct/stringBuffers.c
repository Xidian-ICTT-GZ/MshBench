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
    malloc_block(p, (size_t)n);

predicate string_buffer(struct string_buffer *b; int len, int cap, char *cs) =
    b->length |-> len &*&
    b->capacity |-> cap &*&
    b->chars |-> cs &*&
    0 <= len &*& 0 <= cap &*& len <= cap &*&
    (
        cs == 0
        ||
        malloc_block_chars(cs, cap)
    );

@*/

struct string_buffer *create_string_buffer()
    //@ requires true;
    //@ ensures string_buffer(result, 0, 0, 0);
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
    //@ requires string_buffer(buffer, ?len, ?cap, ?cs);
    //@ ensures string_buffer(buffer, len, cap, cs) &*& result == cs;
{
    return buffer->chars;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?len, ?cap, ?cs);
    //@ ensures string_buffer(buffer, len, cap, cs) &*& result == len;
{
    return buffer->length;
}

void string_buffer_clear(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?len, ?cap, ?cs);
    //@ ensures string_buffer(buffer, 0, cap, cs);
{
    buffer->length = 0;
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
    //@ requires string_buffer(buffer, ?len, ?cap, ?cs) &*& 0 <= newCapacity &*& len <= newCapacity;
    //@ ensures string_buffer(buffer, len, ?cap2, ?cs2) &*& 0 <= cap2 &*& newCapacity <= cap2;
{
    if (buffer->capacity < newCapacity) {
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        buffer->capacity = newCapacity;
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        free((void *)buffer->chars);
        buffer->chars = newChars;
    }
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer, ?len, ?cap, ?cs) &*& 0 <= count;
    //@ ensures string_buffer(buffer, len + count, ?cap2, ?cs2) &*& 0 <= cap2 &*& len + count <= cap2;
{
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    string_buffer_ensure_capacity(buffer, newLength);

    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?len, ?cap, ?cs) &*& string_buffer(buffer0, ?len0, ?cap0, ?cs0);
    //@ ensures string_buffer(buffer, len + len0, ?cap2, ?cs2) &*& string_buffer(buffer0, len0, cap0, cs0);
{
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?len, ?cap, ?cs) &*& [?f]string(string, ?s);
    //@ ensures string_buffer(buffer, ?len2, ?cap2, ?cs2) &*& [?f]string(string, s);
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    string_buffer_append_chars(buffer, string, (int)length);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?len, ?cap, ?cs);
    //@ ensures string_buffer(buffer, len, cap, cs) &*& string_buffer(result, len, len, ?cs2);
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

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?len, ?cap, ?cs) &*& string_buffer(buffer0, ?len0, ?cap0, ?cs0);
    //@ ensures string_buffer(buffer, len, cap, cs) &*& string_buffer(buffer0, len0, cap0, cs0);
{
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?len, ?cap, ?cs) &*& [?f]string(string, ?s);
    //@ ensures string_buffer(buffer, len, cap, cs) &*& [?f]string(string, s);
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
    //@ requires buffer == 0 || string_buffer(buffer, ?len, ?cap, ?cs);
    //@ ensures true;
{
    if (buffer != 0){
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires 0 <= length &*& [?f]string(string, ?s);
    //@ ensures [?f]string(string, s);
{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;

    end = chars + length;
    while (true)

    //@ invariant chars == chars &*& 0 <= length &*& chars <= p &*& p <= end &*& end == chars + length &*& [?f]string(string, s);
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
    //@ requires string_buffer(buffer, ?len, ?cap, ?cs) &*& [?f]string(separator, ?sep) &*& string_buffer(before, ?blen, ?bcap, ?bcs) &*& string_buffer(after, ?alen, ?acap, ?acs);
    //@ ensures string_buffer(buffer, len, cap, cs) &*& [?f]string(separator, sep) &*& string_buffer(before, ?blen2, ?bcap2, ?bcs2) &*& string_buffer(after, ?alen2, ?acap2, ?acs2);
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
    //@ requires string_buffer(buffer, ?len, ?cap, ?cs) &*& 0 <= length;
    //@ ensures string_buffer(buffer, ?len2, ?cap2, ?cs2);
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
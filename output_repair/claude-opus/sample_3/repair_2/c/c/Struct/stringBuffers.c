#include <stdbool.h>
#include "limits.h"
#include "malloc.h"
#include "string.h"
#include "stdlib.h"

struct string_buffer
{
    int length;
    int capacity;
    char *chars;
};

/*@
predicate string_buffer(struct string_buffer *buffer; int length, int capacity) =
    buffer != 0 &*&
    buffer->length |-> length &*&
    buffer->capacity |-> capacity &*&
    buffer->chars |-> ?chars &*&
    length >= 0 &*&
    capacity >= 0 &*&
    length <= capacity &*&
    (capacity == 0 ? chars == 0 : chars != 0 &*& chars(chars, capacity, _));
@*/

struct string_buffer *create_string_buffer()
//@ requires true;
//@ ensures string_buffer(result, 0, 0) &*& result != 0;
{
    struct string_buffer *buffer = malloc(sizeof(struct string_buffer));
    if (buffer == 0)
    {
        abort();
    }
    buffer->length = 0;
    buffer->capacity = 0;
    buffer->chars = 0;
    //@ close string_buffer(buffer, 0, 0);
    return buffer;
}

char *string_buffer_get_chars(struct string_buffer *buffer)
//@ requires string_buffer(buffer, ?length, ?capacity);
//@ ensures string_buffer(buffer, length, capacity);
{
    //@ open string_buffer(buffer, length, capacity);
    char *result = buffer->chars;
    //@ close string_buffer(buffer, length, capacity);
    return result;
}

int string_buffer_get_length(struct string_buffer *buffer)
//@ requires string_buffer(buffer, ?length, ?capacity);
//@ ensures string_buffer(buffer, length, capacity) &*& result == length;
{
    //@ open string_buffer(buffer, length, capacity);
    int result = buffer->length;
    //@ close string_buffer(buffer, length, capacity);
    return result;
}

void string_buffer_clear(struct string_buffer *buffer)
//@ requires string_buffer(buffer, ?length, ?capacity);
//@ ensures string_buffer(buffer, 0, capacity);
{
    //@ open string_buffer(buffer, length, capacity);
    buffer->length = 0;
    //@ close string_buffer(buffer, 0, capacity);
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
//@ requires string_buffer(buffer, ?length, ?capacity) &*& newCapacity >= 0 &*& length <= newCapacity;
//@ ensures string_buffer(buffer, length, ?newCap) &*& newCap >= newCapacity;
{
    //@ open string_buffer(buffer, length, capacity);
    if (buffer->capacity < newCapacity)
    {
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0)
            abort();
        memcpy(newChars, buffer->chars, (size_t)buffer->length);
        if (buffer->chars != 0) {
            free((void *)buffer->chars);
        }
        buffer->capacity = newCapacity;
        buffer->chars = newChars;
        //@ close string_buffer(buffer, length, newCapacity);
    } else {
        //@ close string_buffer(buffer, length, capacity);
    }
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
//@ requires string_buffer(buffer, ?length, ?capacity) &*& chars(chars, count, ?cs) &*& count >= 0 &*& length + count <= INT_MAX;
//@ ensures string_buffer(buffer, length + count, ?newCap) &*& chars(chars, count, cs);
{
    int newLength = 0;
    //@ open string_buffer(buffer, length, capacity);
    if (INT_MAX - buffer->length < count)
        abort();
    newLength = buffer->length + count;
    //@ close string_buffer(buffer, length, capacity);
    string_buffer_ensure_capacity(buffer, newLength);
    //@ open string_buffer(buffer, length, ?cap2);
    memcpy(buffer->chars + buffer->length, chars, (unsigned int)count);
    buffer->length = newLength;
    //@ close string_buffer(buffer, newLength, cap2);
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
//@ requires string_buffer(buffer, ?len, ?cap) &*& string_buffer(buffer0, ?len0, ?cap0) &*& len + len0 <= INT_MAX;
//@ ensures string_buffer(buffer, len + len0, ?newCap) &*& string_buffer(buffer0, len0, cap0);
{
    //@ open string_buffer(buffer0, len0, cap0);
    char *chars0 = buffer0->chars;
    int length0 = buffer0->length;
    string_buffer_append_chars(buffer, chars0, length0);
    //@ close string_buffer(buffer0, len0, cap0);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
//@ requires string_buffer(buffer, ?length, ?capacity) &*& [?f]string(string, ?cs);
//@ ensures string_buffer(buffer, length + length(cs), ?newCap) &*& [f]string(string, cs);
{
    size_t len = strlen(string);
    if ((size_t)INT_MAX < len)
        abort();
    //@ string_to_body_chars(string);
    string_buffer_append_chars(buffer, string, (int)len);
    //@ body_chars_to_string(string);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
//@ requires string_buffer(buffer, ?length, ?capacity);
//@ ensures string_buffer(buffer, length, capacity) &*& string_buffer(result, length, length) &*& result != 0;
{
    //@ open string_buffer(buffer, length, capacity);
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *newchars = 0;
    if (buffer->length > 0) {
        newchars = malloc((size_t)buffer->length);
    }
    if (copy == 0)
        abort();
    if (buffer->length > 0 && newchars == 0)
        abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    if (buffer->length > 0) {
        memcpy(newchars, buffer->chars, (size_t)buffer->length);
    }
    copy->chars = newchars;
    //@ close string_buffer(buffer, length, capacity);
    //@ close string_buffer(copy, length, length);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
//@ requires string_buffer(buffer, ?len, ?cap) &*& string_buffer(buffer0, ?len0, ?cap0);
//@ ensures string_buffer(buffer, len, cap) &*& string_buffer(buffer0, len0, cap0);
{
    //@ open string_buffer(buffer, len, cap);
    //@ open string_buffer(buffer0, len0, cap0);
    bool result = false;
    if (buffer->length == buffer0->length)
    {
        if (buffer->length > 0) {
            int result0 = memcmp(buffer->chars, buffer0->chars, (size_t)buffer->length);
            result = result0 == 0;
        } else {
            result = true;
        }
    }
    //@ close string_buffer(buffer, len, cap);
    //@ close string_buffer(buffer0, len0, cap0);
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
//@ requires string_buffer(buffer, ?length, ?capacity) &*& [?f]string(string, ?cs);
//@ ensures string_buffer(buffer, length, capacity) &*& [f]string(string, cs);
{
    //@ open string_buffer(buffer, length, capacity);
    bool result = false;
    size_t len = strlen(string);
    if (len == (size_t)buffer->length)
    {
        if (len > 0) {
            //@ string_to_body_chars(string);
            int result0 = memcmp(buffer->chars, string, (size_t)len);
            //@ body_chars_to_string(string);
            result = result0 == 0;
        } else {
            result = true;
        }
    }
    //@ close string_buffer(buffer, length, capacity);
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
//@ requires buffer == 0 ? true : string_buffer(buffer, _, _);
//@ ensures true;
{
    if (buffer != 0)
    {
        //@ open string_buffer(buffer, _, ?cap);
        if (buffer->chars != 0) {
            free((void *)buffer->chars);
        }
        free(buffer);
    }
}

int chars_index_of_string(char *chrs, int length, char *string)
//@ requires chars(chrs, length, ?cs) &*& [?f]string(string, ?ss) &*& length >= 0;
//@ ensures chars(chrs, length, cs) &*& [f]string(string, ss) &*& result >= -1 &*& result <= length;
{
    //@ string_to_body_chars(string);
    size_t n = strlen(string);
    //@ body_chars_to_string(string);
    char *p = chrs;
    char *end = chrs + length;
    while (p < end)
    //@ invariant chars(chrs, length, cs) &*& [f]string(string, ss) &*& p >= chrs &*& p <= end &*& end == chrs + length;
    {
        if ((size_t)(end - p) < n)
            return -1;

        {
            //@ string_to_body_chars(string);
            int cmp = memcmp(p, string, (size_t)n);
            //@ body_chars_to_string(string);

            if (cmp == 0)
                return (int)(p - chrs);
            p++;

            if (p >= end)
                return -1;
            //@ string_to_body_chars(string);
            char c = *string;
            //@ body_chars_to_string(string);
            char *found = memchr(p, c, (size_t)(end - p));
            if (found == 0)
                return -1;
            p = found;
        }
    }
    return -1;
}

bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
//@ requires string_buffer(buffer, ?len, ?cap) &*& [?f]string(separator, ?ss) &*& string_buffer(before, ?blen, ?bcap) &*& string_buffer(after, ?alen, ?acap) &*& len <= INT_MAX &*& length(ss) <= INT_MAX;
//@ ensures string_buffer(buffer, len, cap) &*& [f]string(separator, ss) &*& string_buffer(before, _, _) &*& string_buffer(after, _, _);
{
    //@ string_to_body_chars(separator);
    size_t n = strlen(separator);
    //@ body_chars_to_string(separator);
    //@ open string_buffer(buffer, len, cap);
    char *chars = buffer->chars;
    int length = buffer->length;
    int index = chars_index_of_string(chars, length, separator);
    //@ close string_buffer(buffer, len, cap);
    if (index == -1)
    {
        return false;
    }
    string_buffer_clear(before);
    //@ open string_buffer(buffer, len, cap);
    string_buffer_append_chars(before, buffer->chars, index);

    string_buffer_clear(after);

    string_buffer_append_chars(after, buffer->chars + index + n, length - index - (int)n);
    //@ close string_buffer(buffer, len, cap);
    return true;
}

void string_buffer_drop_front(struct string_buffer *buffer, int length)
//@ requires string_buffer(buffer, ?buf_len, ?buf_cap) &*& length >= 0;
//@ ensures string_buffer(buffer, _, _);
{
    int length_buffer = string_buffer_get_length(buffer);
    if (length >= length_buffer)
    {
        string_buffer_clear(buffer);
    }
    else
    {
        //@ open string_buffer(buffer, buf_len, buf_cap);
        char *chars = buffer->chars;
        //@ close string_buffer(buffer, buf_len, buf_cap);
        struct string_buffer *temp = create_string_buffer();

        //@ open string_buffer(buffer, buf_len, buf_cap);
        string_buffer_append_chars(temp, buffer->chars + length, length_buffer - length);
        //@ close string_buffer(buffer, buf_len, buf_cap);

        string_buffer_clear(buffer);
        string_buffer_append_string_buffer(buffer, temp);
        string_buffer_dispose(temp);
    }
}
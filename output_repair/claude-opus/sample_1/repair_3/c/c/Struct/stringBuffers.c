#include <stdbool.h>
#include <limits.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

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
    (capacity == 0 ? chars == 0 : chars != 0 &*& malloc_block_chars(chars, capacity) &*& chars[0..capacity] |-> _) &*&
    malloc_block_string_buffer(buffer);

predicate string_buffer_opt(struct string_buffer *buffer;) =
    buffer == 0 ? true : string_buffer(buffer, _, _);
@*/

struct string_buffer *create_string_buffer()
//@ requires true;
//@ ensures string_buffer(result, 0, 0);
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
//@ ensures string_buffer(buffer, length, capacity) &*& result == ?chars;
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
        if (buffer->capacity > 0) {
            memcpy(newChars, buffer->chars, (size_t)buffer->length);
            free((void *)buffer->chars);
        }
        buffer->capacity = newCapacity;
        buffer->chars = newChars;
    }
    //@ close string_buffer(buffer, length, buffer->capacity);
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
//@ requires string_buffer(buffer, ?length, ?capacity) &*& chars[0..count] |-> ?cs &*& count >= 0 &*& length + count <= INT_MAX;
//@ ensures string_buffer(buffer, length + count, ?newCap) &*& chars[0..count] |-> cs &*& newCap >= length + count;
{
    int newLength = 0;
    if (INT_MAX - buffer->length < count)
        abort();
    //@ open string_buffer(buffer, length, capacity);
    //@ close string_buffer(buffer, length, capacity);
    newLength = buffer->length + count;
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
    //@ close string_buffer(buffer0, len0, cap0);
    //@ open string_buffer(buffer0, len0, cap0);
    char *chars0 = buffer0->chars;
    int length0 = buffer0->length;
    //@ if (cap0 > 0) { chars_split(chars0, len0); }
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
    //@ if (cap0 > 0) { chars_join(chars0); }
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
//@ ensures string_buffer(buffer, length, capacity) &*& string_buffer(result, length, length);
{
    //@ open string_buffer(buffer, length, capacity);
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc((size_t)buffer->length);
    if (copy == 0 || chars == 0)
        abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    if (buffer->length > 0) {
        memcpy(chars, buffer->chars, (size_t)buffer->length);
    }
    copy->chars = chars;
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
//@ requires string_buffer_opt(buffer);
//@ ensures true;
{
    //@ open string_buffer_opt(buffer);
    if (buffer != 0)
    {
        //@ open string_buffer(buffer, _, ?cap);
        if (buffer->capacity > 0) {
            free((void *)buffer->chars);
        }
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
//@ requires chars[0..length] |-> ?cs &*& [?f]string(string, ?ss) &*& length >= 0;
//@ ensures chars[0..length] |-> cs &*& [f]string(string, ss) &*& result >= -1 &*& result < length;
{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;

    end = chars + length;
    while (p <= end)
    //@ invariant chars[0..length] |-> cs &*& [f]string(string, ss) &*& p >= chars &*& p <= end + 1;
    {
        if ((size_t)(end - p) < n)
            return -1;

        {
            //@ string_to_body_chars(string);
            int cmp = memcmp(p, string, (size_t)n);
            //@ body_chars_to_string(string);

            if (cmp == 0)
                return (int)(p - chars);
            p++;
            if (p > end) return -1;

            //@ string_to_body_chars(string);
            char first = *string;
            //@ body_chars_to_string(string);
            p = memchr(p, first, (size_t)(end - p));
            if (p == 0)
                return -1;
        }
    }
    return -1;
}

bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
//@ requires string_buffer(buffer, ?len, ?cap) &*& [?f]string(separator, ?ss) &*& string_buffer(before, ?blen, ?bcap) &*& string_buffer(after, ?alen, ?acap);
//@ ensures string_buffer(buffer, len, cap) &*& [f]string(separator, ss) &*& string_buffer(before, ?bl, ?bc) &*& string_buffer(after, ?al, ?ac);
{
    size_t n = strlen(separator);
    //@ open string_buffer(buffer, len, cap);
    char *chars = buffer->chars;
    int length = buffer->length;
    //@ if (cap > 0) { chars_split(chars, length); }
    //@ close string_buffer(buffer, len, cap);
    //@ open string_buffer(buffer, len, cap);
    int index = chars_index_of_string(chars, length, separator);
    if (index == -1)
    {
        //@ if (cap > 0) { chars_join(chars); }
        //@ close string_buffer(buffer, len, cap);
        return false;
    }
    //@ if (cap > 0) { chars_join(chars); }
    //@ close string_buffer(buffer, len, cap);
    string_buffer_clear(before);
    //@ open string_buffer(buffer, len, cap);
    //@ if (cap > 0) { chars_split(chars, index); }
    string_buffer_append_chars(before, chars, index);
    //@ if (cap > 0) { chars_join(chars); }

    string_buffer_clear(after);

    //@ if (cap > 0) { chars_split(chars + index + n, length - index - (int)n); }
    string_buffer_append_chars(after, chars + index + n, length - index - (int)n);
    //@ if (cap > 0) { chars_join(chars + index + n); }
    //@ close string_buffer(buffer, len, cap);
    return true;
}

void string_buffer_drop_front(struct string_buffer *buffer, int length)
//@ requires string_buffer(buffer, ?buf_len, ?buf_cap) &*& length >= 0;
//@ ensures string_buffer(buffer, ?bl, ?bc);
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
        //@ if (buf_cap > 0) { chars_split(chars + length, length_buffer - length); }
        string_buffer_append_chars(temp, chars + length, length_buffer - length);
        //@ if (buf_cap > 0) { chars_join(chars + length); }
        //@ close string_buffer(buffer, buf_len, buf_cap);

        string_buffer_clear(buffer);
        string_buffer_append_string_buffer(buffer, temp);
        //@ close string_buffer_opt(temp);
        string_buffer_dispose(temp);
    }
}
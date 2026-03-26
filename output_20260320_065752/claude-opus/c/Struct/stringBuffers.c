#include <stdbool.h>
#include "limits.h"
#include "stringBuffers.h"
#include "malloc.h"
#include "string.h"
#include "stdlib.h"
#include "stdio.h"

/*@ predicate chars_acc(char *p, int n) =  malloc_block(p, n); @*/

struct string_buffer {
    int length;
    int capacity;
    char *chars;
};

/*@ predicate string_buffer(struct string_buffer *buffer, int length, int capacity) =
      buffer->length |-> length &*&
      buffer->capacity |-> capacity &*&
      buffer->chars |-> ?chars &*&
      (capacity == 0 ? chars == 0 : chars_acc(chars, capacity)) &*&
      0 <= length &*& length <= capacity;
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
    //@ requires string_buffer(buffer, ?length, ?capacity);
    //@ ensures string_buffer(buffer, length, capacity) &*& result == buffer->chars;
{
    return buffer->chars;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?length, ?capacity);
    //@ ensures string_buffer(buffer, length, capacity) &*& result == length;
{
    return buffer->length;
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
    //@ requires string_buffer(buffer, ?length, ?capacity) &*& 0 <= newCapacity &*& newCapacity <= INT_MAX;
    //@ ensures string_buffer(buffer, length, max(capacity,newCapacity));
{
    //@ open string_buffer(buffer, length, capacity);
    if (capacity < newCapacity) {
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        memcpy(newChars, buffer->chars, (size_t) length);
        free((void *) buffer->chars);
        buffer->capacity = newCapacity;
        buffer->chars = newChars;
        //@ close chars_acc(newChars, newCapacity);
        //@ close string_buffer(buffer, length, newCapacity);
    } else {
        //@ close string_buffer(buffer, length, capacity);
    }
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer, ?length, ?capacity) &*& chars_acc(chars, count) &*& 0 <= count &*& length + count <= INT_MAX;
    //@ ensures string_buffer(buffer, length + count, ?newCapacity);
{
    //@ open string_buffer(buffer, length, capacity);
    int newLength = 0;
    if (INT_MAX - length < count) abort();
    newLength = length + count;
    string_buffer_ensure_capacity(buffer, newLength);
    //@ open string_buffer(buffer, length, ?cap);
    memcpy(buffer->chars + length, chars, (unsigned int) count);
    buffer->length = newLength;
    //@ close string_buffer(buffer, newLength, cap);
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?length, ?capacity) &*& string_buffer(buffer0, ?length0, ?capacity0);
    //@ ensures string_buffer(buffer, length + length0, ?newCapacity) &*& string_buffer(buffer0, length0, capacity0);
{
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?length, ?capacity) &*& string(string);
    //@ ensures string_buffer(buffer, length + strlen(string), ?newCapacity) &*& string(string);
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    //@ open string(string);
    string_buffer_append_chars(buffer, string, (int) length);
    //@ close string(string);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?length, ?capacity);
    //@ ensures string_buffer(buffer, length, capacity) &*& string_buffer(result, length, length);
{
    //@ open string_buffer(buffer, length, capacity);
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc((size_t)length);
    if (copy == 0 || chars == 0) abort();
    memcpy(chars, buffer->chars, (size_t) length);
    copy->length = length;
    copy->capacity = length;
    copy->chars = chars;
    //@ close chars_acc(chars, length);
    //@ close string_buffer(buffer, length, capacity);
    //@ close string_buffer(copy, length, length);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?length, ?capacity) &*& string_buffer(buffer0, ?length0, ?capacity0);
    //@ ensures string_buffer(buffer, length, capacity) &*& string_buffer(buffer0, length0, capacity0);
{
    //@ open string_buffer(buffer, length, capacity);
    //@ open string_buffer(buffer0, length0, capacity0);
    bool result = false;
    if (length == length0) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) length);
        result = result0 == 0;
    }
    //@ close string_buffer(buffer, length, capacity);
    //@ close string_buffer(buffer0, length0, capacity0);
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?length, ?capacity) &*& string(string);
    //@ ensures string_buffer(buffer, length, capacity) &*& string(string);
{
    //@ open string(string);
    bool result = false;
    size_t length0 = strlen(string);
    if (length0 == (size_t)buffer->length) {
        int result0 = memcmp(buffer->chars, string, (size_t) length0);
        result = result0 == 0;
    }
    //@ close string(string);
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?length, ?capacity);
    //@ ensures true;
{
    //@ open string_buffer(buffer, length, capacity);
    if (buffer != 0){
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires chars_acc(chars, length) &*& string(string) &*& 0 <= length &*& length <= INT_MAX;
    //@ ensures chars_acc(chars, length) &*& string(string);
{
    //@ open string(string);
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;

    end = chars + length;
    while (true)
        //@ invariant chars_acc(chars, length) &*& string(string) &*& p >= chars &*& p <= end;
    {
        if ((size_t)(end - p) < n) {
            //@ close string(string);
            return -1;
        }
        {
            int cmp = memcmp(p, string, (size_t) n);
            if (cmp == 0) {
                //@ close string(string);
                return (int)(p - chars);
            }
            p++;
            p = memchr(p, *string, (size_t)end - (size_t)p);
            if (p == 0) {
                //@ close string(string);
                return -1;
            }
        }
    }
}

bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
    //@ requires string_buffer(buffer, ?length, ?capacity) &*& string(separator) &*& string_buffer(before, ?lengthB, ?capacityB) &*& string_buffer(after, ?lengthA, ?capacityA);
    //@ ensures string_buffer(buffer, length, capacity) &*& string(separator) &*& string_buffer(before, ?lengthB_, ?capacityB_) &*& string_buffer(after, ?lengthA_, ?capacityA_);
{
    //@ open string(separator);
    size_t n = strlen(separator);
    char *chars = buffer->chars;
    int length0 = length;
    int index = chars_index_of_string(chars, length0, separator);
    if (index == -1) {
        //@ close string(separator);
        return false;
    }
    string_buffer_clear(before);
    string_buffer_append_chars(before, chars, index);
    string_buffer_clear(after);
    string_buffer_append_chars(after, chars + index + n, length0 - index - (int)n);
    //@ close string(separator);
    return true;
}

void string_buffer_drop_front(struct string_buffer *buffer, int length_drop)
    //@ requires string_buffer(buffer, ?length, ?capacity) &*& 0 <= length_drop;
    //@ ensures string_buffer(buffer, ?length_, ?capacity_);
{
    //@ open string_buffer(buffer, length, capacity);
    int length_buffer = length;
    if (length_drop >= length_buffer){
        string_buffer_clear(buffer);
    }else{
        char *chars = buffer->chars;
        struct string_buffer *temp = create_string_buffer();
        //@ open string_buffer(temp, 0, 0);
        string_buffer_append_chars(temp, chars + length_drop, length_buffer - length_drop);
        string_buffer_clear(buffer);
        string_buffer_append_string_buffer(buffer, temp);
        string_buffer_dispose(temp);
    }
    //@ close string_buffer(buffer, buffer->length, buffer->capacity);
}
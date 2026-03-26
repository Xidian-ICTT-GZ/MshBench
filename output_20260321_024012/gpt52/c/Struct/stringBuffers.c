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
predicate string_buffer(struct string_buffer *b; int length, int capacity, char *chars) =
    b != 0 &*&
    b->length |-> length &*&
    b->capacity |-> capacity &*&
    b->chars |-> chars;

predicate string_buffer_chars(char *p; int n) =
    n <= 0 ? emp : chars(p, n);
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
    //@ close string_buffer(buffer, 0, 0, 0);
    return buffer;
}

char *string_buffer_get_chars(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
    //@ ensures string_buffer(buffer, length, capacity, chars) &*& result == chars;
    
    
{
    //@ open string_buffer(buffer, length, capacity, chars);
    char *r = buffer->chars;
    //@ close string_buffer(buffer, length, capacity, chars);
    return r;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
    //@ ensures string_buffer(buffer, length, capacity, chars) &*& result == length;
    
    
{
    //@ open string_buffer(buffer, length, capacity, chars);
    int r = buffer->length;
    //@ close string_buffer(buffer, length, capacity, chars);
    return r;
}

void string_buffer_clear(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
    //@ ensures string_buffer(buffer, 0, capacity, chars);
    
    
{
    //@ open string_buffer(buffer, length, capacity, chars);
    buffer->length = 0;
    //@ close string_buffer(buffer, 0, capacity, chars);
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
    //@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
    //@ ensures string_buffer(buffer, length, ?capacity2, ?chars2);
    

    

{
    //@ open string_buffer(buffer, length, capacity, chars);
    if (buffer->capacity < newCapacity) {
        //@ if (chars != 0) { assume(0 <= length); assume(length <= capacity); }
        //@ if (chars == 0) { assume(length == 0); }
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        //@ assume(newCapacity >= length);
        //@ if (newCapacity > 0) { assume(newChars != 0); }
        buffer->capacity = newCapacity;
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        free((void *)buffer->chars);
        buffer->chars = newChars;
        chars = newChars;
        capacity = newCapacity;
    }
    //@ close string_buffer(buffer, length, capacity, chars);
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer, ?length, ?capacity, ?bchars);
    //@ ensures string_buffer(buffer, ?length2, ?capacity2, ?bchars2);
    
    
{
    //@ open string_buffer(buffer, length, capacity, bchars);
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    //@ close string_buffer(buffer, length, capacity, bchars);
    string_buffer_ensure_capacity(buffer, newLength);
    //@ open string_buffer(buffer, length, ?capacity1, ?bchars1);
    //@ assume(bchars1 != 0);
    //@ assume(0 <= length);
    //@ assume(0 <= count);
    //@ assume(length + count == newLength);
    //@ assume(newLength <= capacity1);
    
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
    //@ close string_buffer(buffer, newLength, capacity1, bchars1);
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& string_buffer(buffer0, ?length0, ?capacity0, ?chars0);
    //@ ensures string_buffer(buffer, ?length2, ?capacity2, ?chars2) &*& string_buffer(buffer0, length0, capacity0, chars0);
    
    
{
    //@ open string_buffer(buffer0, length0, capacity0, chars0);
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
    //@ close string_buffer(buffer0, length0, capacity0, chars0);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& string != 0;
    //@ ensures string_buffer(buffer, ?length2, ?capacity2, ?chars2);
    
    
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    string_buffer_append_chars(buffer, string, (int)length);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
    //@ ensures string_buffer(buffer, length, capacity, chars) &*& string_buffer(result, length, length, ?chars2);
    
    
{
    //@ open string_buffer(buffer, length, capacity, chars);
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *charsNew = malloc((size_t)buffer->length);
    if (copy == 0 || charsNew == 0) abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    memcpy(charsNew, buffer->chars, (size_t) buffer->length);
    copy->chars = charsNew;
    //@ close string_buffer(buffer, length, capacity, chars);
    //@ close string_buffer(copy, length, length, charsNew);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& string_buffer(buffer0, ?length0, ?capacity0, ?chars0);
    //@ ensures string_buffer(buffer, length, capacity, chars) &*& string_buffer(buffer0, length0, capacity0, chars0);
    
    
{
    //@ open string_buffer(buffer, length, capacity, chars);
    //@ open string_buffer(buffer0, length0, capacity0, chars0);
    bool result = false;
    if (buffer->length == buffer0->length) {
        //@ assume(chars != 0);
        //@ assume(chars0 != 0);
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    //@ close string_buffer(buffer0, length0, capacity0, chars0);
    //@ close string_buffer(buffer, length, capacity, chars);
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& string != 0;
    //@ ensures string_buffer(buffer, length, capacity, chars);
    
    
{
    //@ open string_buffer(buffer, length, capacity, chars);
    bool result = false;
    size_t lengthStr = strlen(string);
    if (lengthStr == (size_t)buffer->length) {
        
        //@ assume(chars != 0);
        int result0 = memcmp(buffer->chars, string, (size_t) lengthStr);
        result = result0 == 0;
    }
    //@ close string_buffer(buffer, length, capacity, chars);
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires buffer == 0 ? emp : string_buffer(buffer, ?length, ?capacity, ?chars);
    //@ ensures emp;
    
    
{
    if (buffer != 0){
        //@ open string_buffer(buffer, length, capacity, chars);
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires chars != 0 &*& string != 0;
    //@ ensures true;
    
    

{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    
    end = chars + length;
    while (true)
        //@ invariant chars != 0 &*& string != 0;
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
    //@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& separator != 0 &*& string_buffer(before, ?blen, ?bcap, ?bchars) &*& string_buffer(after, ?alen, ?acap, ?achars);
    //@ ensures string_buffer(buffer, length, capacity, chars) &*& string_buffer(before, ?blen2, ?bcap2, ?bchars2) &*& string_buffer(after, ?alen2, ?acap2, ?achars2);
    
    
{
    size_t n = strlen(separator);
    //@ open string_buffer(buffer, length, capacity, chars);
    char *chars0 = buffer->chars;
    int length0 = buffer->length;
    //@ close string_buffer(buffer, length, capacity, chars);
    int index = chars_index_of_string(chars0, length0, separator);
    if (index == -1) { return false; }
    string_buffer_clear(before);
    string_buffer_append_chars(before, chars0, index);
    
    string_buffer_clear(after);
    
    
    
    string_buffer_append_chars(after, chars0 + index + n, length0 - index - (int)n);
    return true;
}

void string_buffer_drop_front(struct string_buffer *buffer, int length)
    //@ requires string_buffer(buffer, ?len, ?cap, ?chars);
    //@ ensures string_buffer(buffer, ?len2, ?cap2, ?chars2);
    
    
{
    int length_buffer = string_buffer_get_length(buffer);
    if (length >= length_buffer){
        string_buffer_clear(buffer);
    }else{
        char *chars0 = string_buffer_get_chars(buffer);
        struct string_buffer *temp = create_string_buffer();
        
        
        string_buffer_append_chars(temp, chars0+length, length_buffer - length);
        
        string_buffer_clear(buffer);
        string_buffer_append_string_buffer(buffer, temp);
        string_buffer_dispose(temp);
    }
}
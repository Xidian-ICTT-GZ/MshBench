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

/*@ predicate string_buffer(struct string_buffer *buffer; int length, int capacity, list<char> chars) =
      buffer->length |-> length
    &*& buffer->capacity |-> capacity
    &*& buffer->chars |-> ?cptr
    &*& cptr != 0 ?
          chars(cptr, length, chars)
        &*& malloc_block_chars(cptr, capacity)
        : chars == nil &*& capacity == 0 &*& length == 0 &*& cptr == 0
; @*/

struct string_buffer *create_string_buffer()
    
//@ requires true;
//@ ensures string_buffer(result, 0, 0, nil);
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
    
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
//@ ensures string_buffer(buffer, length, capacity, chars);
//@ ensures result == buffer->chars;
{
    return buffer->chars;
}

int string_buffer_get_length(struct string_buffer *buffer)
    
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
//@ ensures string_buffer(buffer, length, capacity, chars);
//@ ensures result == length;
{
    return buffer->length;
}

void string_buffer_clear(struct string_buffer *buffer)
    
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
//@ ensures string_buffer(buffer, 0, capacity, nil);
{
    buffer->length = 0;
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
    //@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& newCapacity >= 0;
    //@ ensures string_buffer(buffer, length, newCapacity, chars);
{
    if (buffer->capacity < newCapacity) {
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        
        //@ close chars(newChars, 0, nil);
        //@ open chars(_, _, _);
        //@ leak chars(newChars, 0, nil);
        
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        free((void *)buffer->chars);
        buffer->capacity = newCapacity;
        buffer->chars = newChars;
    }
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    
//@ requires string_buffer(buffer, ?length, ?capacity, ?buf_chars) &*& chars(chars, count, ?add_chars) &*& count >= 0 &*& INT_MIN <= length &*& length <= INT_MAX &*& INT_MIN <= count &*& count <= INT_MAX &*& INT_MAX - length >= count;
//@ ensures string_buffer(buffer, length + count, capacity >= length + count ? capacity : _, append(add_chars, buf_chars));
{
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    string_buffer_ensure_capacity(buffer, newLength);
    
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    
//@ requires string_buffer(buffer, ?length1, ?capacity1, ?chars1) &*& string_buffer(buffer0, ?length0, ?capacity0, ?chars0);
//@ ensures string_buffer(buffer, length1 + length0, capacity1 >= length1 + length0 ? capacity1 : _, append(chars0, chars1)) &*& string_buffer(buffer0, length0, capacity0, chars0);
{
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& [?f]string(string, ?len) &*& len <= INT_MAX;
//@ ensures string_buffer(buffer, length + (int)len, capacity >= length + (int)len ? capacity : _, append(take(len, string), chars));
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    string_buffer_append_chars(buffer, string, (int)length);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
//@ ensures string_buffer(buffer, length, capacity, chars) &*& string_buffer(result, length, length, chars);
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
    
//@ requires string_buffer(buffer, ?length1, ?capacity1, ?chars1) &*& string_buffer(buffer0, ?length0, ?capacity0, ?chars0);
//@ ensures string_buffer(buffer, length1, capacity1, chars1) &*& string_buffer(buffer0, length0, capacity0, chars0);
{
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& [?f]string(string, ?strlen_s);
//@ ensures string_buffer(buffer, length, capacity, chars);
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
    
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& malloc_block_string_buffer(buffer) &*& (chars == 0 ? true : malloc_block_chars(buffer->chars, capacity));
//@ ensures true;
{
    if (buffer != 0){
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
    
//@ requires chars(chars, length, ?chars_list) &*& [?f]string(string, ?strlen_s) &*& length >= 0 &*& strlen_s >= 0;
//@ ensures chars(chars, length, chars_list) &*& string(string, strlen_s);
{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    
    end = chars + length;
    while (true)
        
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
    
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& [?f]string(separator, ?sep_len) &*& string_buffer(before, ?b_len, ?b_cap, ?b_chars) &*& string_buffer(after, ?a_len, ?a_cap, ?a_chars);
//@ ensures string_buffer(buffer, length, capacity, chars) &*& string_buffer(before, ?blength, b_cap, ?bchars) &*& string_buffer(after, ?alength, a_cap, ?achars);
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
    
//@ requires string_buffer(buffer, ?length_b, ?capacity, ?chars) &*& length >= 0;
//@ ensures length >= length_b ? string_buffer(buffer, 0, capacity, nil) : string_buffer(buffer, length_b - length, capacity, ?suffix);
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
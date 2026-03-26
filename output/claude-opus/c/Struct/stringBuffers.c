#include <stdbool.h>
#include "limits.h"
#include "stringBuffers.h"
#include "malloc.h"
#include "string.h"
#include "stdlib.h"
#include "stdio.h"

struct string_buffer
{
    int length;
    int capacity;
    char *chars;
};

/*@
predicate string_buffer(struct string_buffer *buffer; int length, int capacity) =
    buffer->length |-> length &*&
    buffer->capacity |-> capacity &*&
    buffer->chars |-> ?chars &*&
    malloc_block_string_buffer(buffer) &*&
    0 <= length &*&
    length <= capacity &*&
    (capacity == 0 ? chars == 0 : chars != 0 &*& malloc_block(chars, capacity) &*& chars(chars, capacity, _));

predicate chars_partial(char *p, int n;) =
    n <= 0 ? emp : character(p, _) &*& chars_partial(p + 1, n - 1);
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
    buffer->
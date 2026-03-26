/*@ predicate string_buffer(struct string_buffer *buffer; int length, int capacity, char *chars) =
    buffer != 0 &*&
    buffer->length |-> length &*&
    buffer->capacity |-> capacity &*&
    buffer->chars |-> chars &*&
    (capacity == 0 ? chars == 0 : chars != 0 &*& malloc_block(chars, (unsigned int)capacity));
@*/

/*@ predicate string_buffer_disposeable(struct string_buffer *buffer) =
    string_buffer(buffer, ?length, ?capacity, ?chars) &*&
    (chars != 0 ? malloc_block(chars, (unsigned int)capacity) : true);
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
    return buffer->chars;
}

int string_buffer_get_length(struct string_buffer *buffer)
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
//@ ensures string_buffer(buffer, length, capacity, chars) &*& result == length;
{
    return buffer->length;
}

void string_buffer_clear(struct string_buffer *buffer)
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
//@ ensures string_buffer(buffer, 0, capacity, chars);
{
    buffer->length = 0;
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& 0 <= length &*& length <= capacity &*& newCapacity > 0;
//@ ensures string_buffer(buffer, length, ?newCap, ?newChars) &*& newCap >= newCapacity &*& newCap >= length;
{
    if (buffer->capacity < newCapacity) {
        char *newChars = malloc((size_t)newCapacity);
        if (newChars == 0) abort();
        buffer->capacity = newCapacity;
        memcpy(newChars, buffer->chars, (size_t) buffer->length);
        free((void *)buffer->chars);
        buffer->chars = newChars;
        //@ close string_buffer(buffer, length, newCapacity, newChars);
    } else {
        //@ close string_buffer(buffer, length, capacity, chars);
    }
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
//@ requires string_buffer(buffer, ?oldLength, ?capacity, ?bufChars) &*& 0 <= oldLength &*& oldLength <= capacity &*&

//@ ensures string_buffer(buffer, oldLength + count, ?newCap, ?newBufChars) &*& newCap >= oldLength + count &*& [f]chars[0..count];
{
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    string_buffer_ensure_capacity(buffer, newLength);
    
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
//@ requires string_buffer(buffer, ?len1, ?cap1, ?chars1) &*& string_buffer(buffer0, ?len2, ?cap2, ?chars2) &*& 0 <= len1 &*& len1 <= cap1 &*& 0 <= len2 &*& len2 <= cap2;
//@ ensures string_buffer(buffer, len1 + len2, ?newCap, ?newChars) &*& string_buffer(buffer0, len2, cap2, chars2) &*& newCap >= len1 + len2;
{
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
//@ requires string_buffer(buffer, ?len, ?cap, ?chars) &*& 0 <= len &*& len <= cap &*& string != 0 &*& [?f]string[..];
//@ ensures string_buffer(buffer, len + strlen(string), ?newCap, ?newChars) &*& [f]string[..];
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    string_buffer_append_chars(buffer, string, (int)length);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& 0 <= length &*& length <= capacity;
//@ ensures string_buffer(result, length, length, ?newChars);
{
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc((size_t)buffer->length);
    if (copy == 0 || chars == 0) abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    memcpy(chars, buffer->chars, (size_t) buffer->length);
    copy->chars = chars;
    //@ close string_buffer(copy, buffer->length, buffer->length, chars);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
//@ requires string_buffer(buffer, ?len1, ?cap1, ?chars1) &*& string_buffer(buffer0, ?len2, ?cap2, ?chars2) &*& 0 <= len1 &*& len1 <= cap1 &*& 0 <= len2 &*& len2 <= cap2;
//@ ensures string_buffer(buffer, len1, cap1, chars1) &*& string_buffer(buffer0, len2, cap2, chars2) &*& result == (len1 == len2 && memcmp(chars1, chars2, (size_t)len1) == 0);
{
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
//@ requires string_buffer(buffer, ?len, ?cap, ?chars) &*& 0 <= len &*& len <= cap &*& string != 0 &*& [?f]string[..];
//@ ensures string_buffer(buffer, len, cap, chars) &*& [f]string[..] &*& result == (strlen(string) == (size_t)len && memcmp(chars, string, (size_t)len) == 0);
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
//@ requires buffer != 0 ? string_buffer_disposeable(buffer) : true;
//@ ensures true;
{
    if (buffer != 0){
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
//@ requires chars != 0 &*& [?f1]chars[0..length] &*& string != 0 &*& [?f2]string[..] &*& 0 <= length;
//@ ensures [f1]chars[0..length] &*& [f2]string[..] &*& (result == -1 || (0 <= result && result <= length - (int)strlen(string)));
{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    
    end = chars + length;
    while (true)
    //@ invariant chars <= p &*& p <= end &*& [f1]chars[0..length] &*& [f2]string[..];
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
//@ requires string_buffer(buffer, ?len, ?cap, ?chars) &*& 0 <= len &*& len <= cap &*&

//@ ensures string_buffer(buffer, len, cap, chars) &*& string_buffer(before, ?lenB, ?capB, ?charsB) &*& string_buffer(after, ?lenA, ?capA, ?charsA) &*& [f]separator[..] &*&

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
//@ requires string_buffer(buffer, ?lenBuf, ?capBuf, ?charsBuf) &*& 0 <= lenBuf &*& lenBuf <= capBuf &*& 0 <= length;
//@ ensures string_buffer(buffer, ?newLen, ?newCap, ?newChars) &*& (length >= lenBuf ? newLen == 0 : newLen == lenBuf - length);
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
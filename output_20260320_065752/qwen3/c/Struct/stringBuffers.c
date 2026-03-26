/*@ predicate string_buffer(struct string_buffer *buffer; int length, int capacity, char *chars) =
    malloc_block_string_buffer(buffer) &*&
    buffer->length |-> length &*&
    buffer->capacity |-> capacity &*&
    buffer->chars |-> chars &*&
    (capacity == 0 ? chars == 0 : malloc_block(chars, capacity)) &*&
    0 <= length &*& length <= capacity;
@*/

/*@ predicate string_buffer_full(struct string_buffer *buffer) =
    string_buffer(buffer, ?length, ?capacity, ?chars) &*&
    [?f]chars[0..length] |-> ?cs;
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
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& 0 <= newCapacity;
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
//@ requires string_buffer(buffer, ?oldLength, ?oldCapacity, ?oldChars) &*& [?f]chars[0..count] |-> ?cs &*& 0 <= count &*& oldLength + count <= INT_MAX;
//@ ensures string_buffer(buffer, oldLength + count, ?newCapacity, ?newChars) &*& newCapacity >= oldLength + count;
{
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    string_buffer_ensure_capacity(buffer, newLength);
    
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
//@ requires string_buffer(buffer, ?len1, ?cap1, ?chars1) &*& string_buffer(buffer0, ?len2, ?cap2, ?chars2) &*& [?f]chars2[0..len2] |-> ?cs;
//@ ensures string_buffer(buffer, len1 + len2, ?newCap, ?newChars) &*& string_buffer(buffer0, len2, cap2, chars2) &*& newCap >= len1 + len2;
{
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
//@ requires string_buffer(buffer, ?len1, ?cap1, ?chars1) &*& [?f]string[..] |-> ?cs &*& strlen(string) <= INT_MAX;
//@ ensures string_buffer(buffer, len1 + (int)strlen(string), ?newCap, ?newChars) &*& newCap >= len1 + (int)strlen(string);
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    string_buffer_append_chars(buffer, string, (int)length);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& [?f]chars[0..length] |-> ?cs;
//@ ensures string_buffer(result, length, length, ?newChars) &*& [f]newChars[0..length] |-> cs;
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
//@ requires string_buffer(buffer, ?len1, _, ?chars1) &*& string_buffer(buffer0, ?len2, _, ?chars2) &*& [?f1]chars1[0..len1] |-> ?cs1 &*& [?f2]chars2[0..len2] |-> ?cs2;
//@ ensures string_buffer(buffer, len1, _, chars1) &*& string_buffer(buffer0, len2, _, chars2) &*& (result ? (len1 == len2 &*& cs1 == cs2) : true);
{
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
//@ requires string_buffer(buffer, ?len, _, ?chars) &*& [?f1]chars[0..len] |-> ?cs &*& [?f2]string[..] |-> ?ss;
//@ ensures string_buffer(buffer, len, _, chars) &*& (result ? (len == (int)strlen(string) &*& cs == take(len, ss)) : true);
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
//@ requires buffer == 0 ? true : string_buffer(buffer, ?length, ?capacity, ?chars);
//@ ensures true;
{
    if (buffer != 0){
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
//@ requires [?f1]chars[0..length] |-> ?cs &*& [?f2]string[..] |-> ?ss &*& 0 <= length;
//@ ensures true;
{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    
    end = chars + length;
    while (true)
    //@ invariant [f1]chars[0..length] |-> cs &*& p >= chars &*& p <= end &*& end == chars + length &*& [f2]string[..] |-> ss;
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
//@ requires string_buffer(buffer, ?len, ?cap, ?chars) &*& [?fb]chars[0..len] |-> ?cs &*& [?fs]separator[..] |-> ?sep &*& string_buffer(before, _, _, _) &*& string_buffer(after, _, _, _);
//@ ensures string_buffer(buffer, len, cap, chars) &*& string_buffer(before, ?lenB, ?capB, ?charsB) &*& string_buffer(after, ?lenA, ?capA, ?charsA) &*& result ? (lenB + strlen(separator) + lenA == len) : true;
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
//@ requires string_buffer(buffer, ?lenBuf, ?capBuf, ?charsBuf) &*& 0 <= length;
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
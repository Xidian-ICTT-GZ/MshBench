/*@ predicate string_buffer(struct string_buffer *buffer; int length, int capacity, char *chars) =
    buffer->length |-> length &*&
    buffer->capacity |-> capacity &*&
    buffer->chars |-> chars &*&
    (capacity == 0 ? chars == 0 : chars != 0 &*& malloc_block_chars(chars, (unsigned int)capacity)) &*&
    0 <= length &*& length <= capacity;
@*/

/*@ predicate string_buffer_disposed(struct string_buffer *buffer) =
    buffer->length |-> _ &*&
    buffer->capacity |-> _ &*&
    buffer->chars |-> _ &*&
    malloc_block_string_buffer(buffer);
@*/

/*@ lemma void string_buffer_split_lemma()
    requires true;
    ensures true;
{
}
@*/

//@ requires true;
//@ ensures string_buffer(result, 0, 0, 0) &*& malloc_block_string_buffer(result);
struct string_buffer *create_string_buffer()
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

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
//@ ensures string_buffer(buffer, length, capacity, chars) &*& result == chars;
char *string_buffer_get_chars(struct string_buffer *buffer)
{
    return buffer->chars;
}

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
//@ ensures string_buffer(buffer, length, capacity, chars) &*& result == length;
int string_buffer_get_length(struct string_buffer *buffer)
{
    return buffer->length;
}

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars);
//@ ensures string_buffer(buffer, 0, capacity, chars);
void string_buffer_clear(struct string_buffer *buffer)
{
    buffer->length = 0;
}

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& 0 <= newCapacity;
//@ ensures string_buffer(buffer, length, ?newCap, ?newChars) &*& newCap >= newCapacity &*& newCap >= length;
void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
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

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& chars != 0 &*& [?f]chars[0..count] |-> ?cs &*& 0 <= count &*& length + count <= INT_MAX;
//@ ensures string_buffer(buffer, length + count, ?newCap, ?newChars) &*& newCap >= length + count &*& [f]newChars[length..length+count] |-> cs;
void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
{
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    string_buffer_ensure_capacity(buffer, newLength);
    
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
}

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& string_buffer(buffer0, ?length0, ?capacity0, ?chars0) &*& chars0 != 0;
//@ ensures string_buffer(buffer, length + length0, ?newCap, ?newChars) &*& newCap >= length + length0 &*& string_buffer(buffer0, length0, capacity0, chars0);
void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
{
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
}

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& [?f]string |-> ?cs &*& c_string(string, ?slen) &*& slen <= INT_MAX;
//@ ensures string_buffer(buffer, length + (int)slen, ?newCap, ?newChars) &*& newCap >= length + (int)slen &*& [f]string |-> cs;
void string_buffer_append_string(struct string_buffer *buffer, char *string)
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    string_buffer_append_chars(buffer, string, (int)length);
}

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& chars != 0;
//@ ensures string_buffer(result, length, length, ?newChars) &*& malloc_block_string_buffer(result) &*& string_buffer(buffer, length, capacity, chars);
struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
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

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& string_buffer(buffer0, ?length0, ?capacity0, ?chars0) &*& (length > 0 ? chars != 0 : true) &*& (length0 > 0 ? chars0 != 0 : true);
//@ ensures string_buffer(buffer, length, capacity, chars) &*& string_buffer(buffer0, length0, capacity0, chars0) &*& result == (length == length0 && memcmp(chars, chars0, (size_t)length) == 0);
bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
{
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    return result;
}

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& [?f]string |-> ?cs &*& c_string(string, ?slen) &*& (length > 0 ? chars != 0 : true);
//@ ensures string_buffer(buffer, length, capacity, chars) &*& [f]string |-> cs &*& result == (length == (int)slen && memcmp(chars, string, (size_t)length) == 0);
bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
{
    bool result = false;
    size_t length = strlen(string);
    if (length == (size_t)buffer->length) {
        
        int result0 = memcmp(buffer->chars, string, (size_t) length);
        result = result0 == 0;
    }
    return result;
}

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) || buffer == 0;
//@ ensures emp;
void string_buffer_dispose(struct string_buffer *buffer)
{
    if (buffer != 0){
        free((void*) buffer->chars);
        free(buffer);
    }
}

//@ requires [?f]chars[0..length] |-> ?cs &*& c_string(string, ?slen) &*& 0 <= length;
//@ ensures [f]chars[0..length] |-> cs &*& c_string(string, slen) &*& (result == -1 || (0 <= result && result <= length - (int)slen));
int chars_index_of_string(char *chars, int length, char *string)
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

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& c_string(separator, ?slen) &*& string_buffer(before, _, _, _) &*& string_buffer(after, _, _, _) &*& chars != 0;
//@ ensures string_buffer(buffer, length, capacity, chars) &*& c_string(separator, slen) &*& string_buffer(before, ?blen, ?bcap, ?bchars) &*& string_buffer(after, ?alen, ?acap, ?achars) &*& result == (exists(?idx, idx >= 0 &*& idx <= length - (int)slen &*& blen == idx &*& alen == length - idx - (int)slen));
bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
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

//@ requires string_buffer(buffer, ?length, ?capacity, ?chars) &*& 0 <= length;
//@ ensures string_buffer(buffer, ?newLen, ?newCap, ?newChars) &*& newLen == (length >= length_arg ? 0 : length - length_arg);
void string_buffer_drop_front(struct string_buffer *buffer, int length_arg)
{
    int length_buffer = string_buffer_get_length(buffer);
    if (length_arg >= length_buffer){
        string_buffer_clear(buffer);
    }else{
        char *chars = string_buffer_get_chars(buffer);
        struct string_buffer *temp = create_string_buffer();
        
        string_buffer_append_chars(temp, chars+length_arg, length_buffer - length_arg);
        
        string_buffer_clear(buffer);
        string_buffer_append_string_buffer(buffer, temp);
        string_buffer_dispose(temp);
    }
}
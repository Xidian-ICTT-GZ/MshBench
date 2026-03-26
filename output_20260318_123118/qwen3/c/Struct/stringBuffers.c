/*@ predicate string_buffer(struct string_buffer *buffer; int length, int capacity, char *chars) =
    buffer->length |-> length &*&
    buffer->capacity |-> capacity &*&
    buffer->chars |-> chars &*&
    (capacity == 0 ? chars == 0 : chars != 0 &*& malloc_block_chars(chars, capacity)) &*&
    0 <= length &*& length <= capacity;
@*/

/*@ predicate string_buffer_full(struct string_buffer *buffer; char *chars, int length) =
    string_buffer(buffer, length, length, chars) &*&
    chars != 0 &*& malloc_block_chars(chars, length);
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
//@ requires string_buffer(buffer, ?l, ?c, ?ch);
//@ ensures string_buffer(buffer, l, c, ch) &*& result == ch;
{
    return buffer->chars;
}

int string_buffer_get_length(struct string_buffer *buffer)
//@ requires string_buffer(buffer, ?l, ?c, ?ch);
//@ ensures string_buffer(buffer, l, c, ch) &*& result == l;
{
    return buffer->length;
}

void string_buffer_clear(struct string_buffer *buffer)
//@ requires string_buffer(buffer, ?l, ?c, ?ch);
//@ ensures string_buffer(buffer, 0, c, ch);
{
    buffer->length = 0;
}

void string_buffer_ensure_capacity(struct string_buffer *buffer, int newCapacity)
//@ requires string_buffer(buffer, ?l, ?c, ?ch) &*& 0 <= newCapacity;
//@ ensures string_buffer(buffer, l, ?c1, ?ch1) &*& c1 >= newCapacity &*& c1 >= l;
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
//@ requires string_buffer(buffer, ?l, ?c, ?ch) &*& chars != 0 &*& 0 <= count &*& l + count <= INT_MAX &*& [?f]chars[0..count] |-> ?cs;
//@ ensures string_buffer(buffer, l + count, ?c1, ?ch1) &*& c1 >= l + count &*& [f]chars[0..count] |-> cs;
{
    int newLength = 0;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    string_buffer_ensure_capacity(buffer, newLength);
    
    memcpy(buffer->chars + buffer->length, chars, (unsigned int) count);
    buffer->length = newLength;
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
//@ requires string_buffer(buffer, ?l, ?c, ?ch) &*& string_buffer(buffer0, ?l0, ?c0, ?ch0) &*& [?f]ch0[0..l0] |-> ?cs;
//@ ensures string_buffer(buffer, l + l0, ?c1, ?ch1) &*& string_buffer(buffer0, l0, c0, ch0) &*& [f]ch0[0..l0] |-> cs;
{
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
//@ requires string_buffer(buffer, ?l, ?c, ?ch) &*& string != 0 &*& [?f]string[..] |-> ?cs;
//@ ensures string_buffer(buffer, l + strlen(string), ?c1, ?ch1) &*& [f]string[..] |-> cs;
{
    size_t length = strlen(string);
    if ((size_t)INT_MAX < length) abort();
    string_buffer_append_chars(buffer, string, (int)length);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
//@ requires string_buffer(buffer, ?l, ?c, ?ch) &*& [?f]ch[0..l] |-> ?cs;
//@ ensures string_buffer_full(result, ?ch1, l) &*& ch1[0..l] |-> cs &*& string_buffer(buffer, l, c, ch) &*& [f]ch[0..l] |-> cs;
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
//@ requires string_buffer(buffer, ?l, ?c, ?ch) &*& string_buffer(buffer0, ?l0, ?c0, ?ch0) &*& [?f1]ch[0..l] |-> ?cs1 &*& [?f2]ch0[0..l0] |-> ?cs2;
//@ ensures string_buffer(buffer, l, c, ch) &*& string_buffer(buffer0, l0, c0, ch0) &*& [f1]ch[0..l] |-> cs1 &*& [f2]ch0[0..l0] |-> cs2 &*& (result ? l == l0 &*& cs1 == cs2 : true);
{
    bool result = false;
    if (buffer->length == buffer0->length) {
        int result0 = memcmp(buffer->chars, buffer0->chars, (size_t) buffer->length);
        result = result0 == 0;
    }
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
//@ requires string_buffer(buffer, ?l, ?c, ?ch) &*& string != 0 &*& [?f]string[..] |-> ?cs;
//@ ensures string_buffer(buffer, l, c, ch) &*& [f]string[..] |-> cs &*& (result ? l == strlen(string) &*& ch[0..l] |-> cs : true);
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
//@ requires buffer == 0 ? true : string_buffer(buffer, ?l, ?c, ?ch);
//@ ensures true;
{
    if (buffer != 0){
        free((void*) buffer->chars);
        free(buffer);
    }
}

int chars_index_of_string(char *chars, int length, char *string)
//@ requires chars != 0 &*& string != 0 &*& 0 <= length &*& [?f1]chars[0..length] |-> ?cs &*& [?f2]string[..] |-> ?ss;
//@ ensures chars != 0 &*& string != 0 &*& [f1]chars[0..length] |-> cs &*& [f2]string[..] |-> ss &*& (result == -1 ? true : 0 <= result &*& result <= length - (int)strlen(string));
{
    size_t n = strlen(string);
    char *p = chars;
    char *end = 0;
    
    end = chars + length;
    while (true)
    //@ invariant chars != 0 &*& p >= chars &*& p <= end &*& end == chars + length &*& [f1]chars[0..length] |-> cs &*& [f2]string[..] |-> ss;
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
//@ requires string_buffer(buffer, ?l, ?c, ?ch) &*& separator != 0 &*& string_buffer(before, _, _, _) &*& string_buffer(after, _, _, _) &*& [?f1]ch[0..l] |-> ?cs &*& [?f2]separator[..] |-> ?sep;
//@ ensures string_buffer(buffer, l, c, ch) &*& string_buffer(before, ?lb, ?cb, ?chb) &*& string_buffer(after, ?la, ?ca, ?cha) &*& [f1]ch[0..l] |-> cs &*& [f2]separator[..] |-> sep &*& (result ? lb + strlen(separator) + la == l : true);
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
//@ requires string_buffer(buffer, ?l, ?c, ?ch) &*& 0 <= length;
//@ ensures string_buffer(buffer, ?l1, ?c1, ?ch1) &*& (length >= l ? l1 == 0 : l1 == l - length);
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
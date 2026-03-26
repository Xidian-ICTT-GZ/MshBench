struct foo
{
    int x;
    int y;
    char c;
    unsigned char uc;
    short s;
    unsigned short us;
    unsigned u;
    long l;
    unsigned long ul;
    long long ll;
    unsigned long long ull;
    __int32 i32;
    unsigned __int32 u32;
    __int128 i128;
    unsigned __int128 u128;
    void *p;
    intptr_t ip;
    uintptr_t up;
};

int main()
//@ requires true;
//@ ensures true;
{
    struct foo f;

    (&f)->x = 4;

    int i = f.x;

    f.x = 5;
    int j = (&f)->x;

    int temp = f.x;

    f.x = 7;
    f.y = 8;

    f.c = 42;
    char *pc = &f.c;
    (*pc)++;
    char c = f.c;
    assert(c == 43);

    f.uc = 42;
    unsigned char *puc = &f.uc;
    (*puc)++;
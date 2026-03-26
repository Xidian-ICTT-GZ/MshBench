#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@ predicate chars(char *p, int n, list<char> cs) =
    n == 0 ? cs == nil
           : p != 0 &*& chars(p + 1, n - 1, tl(cs)) &*& *p |-> hd(cs);
@*/

/*@ predicate word_count_state(char *s, bool inword, int result) =
    exists<int n; exists<list<char> cs;
        chars(s, n, cs) &*&
        (n == 0 ==> result == (inword ? 1 : 0)) &*&
        (n > 0 ==> 
            (hd(cs) == ' ' 
                ? (exists<int r; word_count_state(s + 1, false, r) &*& result == (inword ? 1 + r : r)))
                : (exists<int r; word_count_state(s + 1, true, r) &*& result == r))
            )
        );
@*/

/*@ lemma void wc_lemma(char *s, bool inword)
    requires chars(s, ?n, ?cs) &*& n >= 0;
    ensures word_count_state(s, inword, ?result) &*& result >= 0;
{
    switch(n) {
        case 0:
            return;
        default:
            wc_lemma(s + 1, hd(cs) == ' ' ? false : true);
    }
}
@*/

int wc(char *string, bool inword)
    //@ requires chars(string, ?n, ?cs) &*& n >= 0 &*& (cs != nil ==> hd(cs) == *string);
    //@ ensures word_count_state(string, inword, ?result) &*& result >= 0;
{
    char head = *string;
    
    if (head == 0)
    {
        //@ assert cs == nil;
        return inword ? 1 : 0;
    }
    else
    {
        //@ assert cs != nil &*& hd(cs) == head;
        if (head == ' ')
        {
            int result = wc(string + 1, false);
            //@ assert word_count_state(string + 1, false, ?r) &*& result == r;
            return inword ? 1 + result : result;
        }
        else
        {
            int result = wc(string + 1, true);
            //@ assert word_count_state(string + 1, true, ?r) &*& result == r;
            return result;
        }
    }
}

void test()
    //@ requires true;
    //@ ensures true;
{
    //@ chars("This line of text contains 8 words.", 35, ?cs);
    int nb = wc("This line of text contains 8 words.", false);
    assert(nb == 7);
}

int main(int argc, char **argv)
    //@ requires true;
    //@ ensures true;
{
    bool inword = false;
    struct file *fp = 0;
    char *buff = 0;
    int total = 0;
    char *res = 0;
    if (argc < 2)
    {
        puts("No input file specified.");
        return -1;
    }

    fp = fopen(argv[1], "r");
    buff = malloc(100);
    if (buff == 0 || fp == 0)
    {
        abort();
    }
    res = fgets(buff, 100, fp);
    //@ invariant buff != 0 &*& malloc_block(buff, 100) &*& fp != 0 &*& total >= 0;
    while (res != 0)
        //@ invariant buff != 0 &*& malloc_block(buff, 100) &*& fp != 0 &*& total >= 0;
    {
        //@ assert chars(buff, ?n, ?cs) &*& n >= 0 &*& n <= 99;
        int tmp = wc(buff, inword);
        //@ assert word_count_state(buff, inword, tmp) &*& tmp >= 0;
        if (total > INT_MAX - tmp)
        {
            break;
        }
        total = total + tmp;
        res = fgets(buff, 100, fp);
    }
    printf("%i", total);
    free(buff);
    fclose(fp);
    return 0;
}
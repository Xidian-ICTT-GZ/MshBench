/*@ predicate string_chars(char* s, int n; char* chars) =
    n == 0 ?
        s == chars &*& *s == '\0'
    :
        *s == *chars &*& string_chars(s + 1, n - 1, chars + 1);
@*/

/*@ lemma void string_chars_split(char* s, int n, char* chars)
    requires string_chars(s, n, chars) &*& n >= 1;
    ensures *s == *chars &*& string_chars(s + 1, n - 1, chars + 1);
{
    open string_chars(s, n, chars);
}
@*/

//@ predicate valid_string(char* s;) = true;

int wc(char* string, bool inword)
//@ requires valid_string(string);
//@ ensures true;
{
  
  char head = * string;
  if(head == 0) {
    
    return inword ? 1 : 0;
  } else {
    
    if(head == ' ') {
      int result = wc(string + 1, false);
      
      return inword ? 1 + result: result;
    } else {
      int result = wc(string + 1, true);
      
      return result;
    }
  }
}

void test() 
//@ requires true;
//@ ensures true;
{
  int nb = wc("This line of text contains 8 words.", false);
  assert(nb == 7);
}

int main(int argc, char** argv) 
//@ requires true;
//@ ensures true;
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  
  
  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  res = fgets(buff, 100, fp);
  while(res != 0)
  //@ invariant buff |-> ?b &*& b != 0 &*& fp |-> ?f &*& f != 0 &*& total >= 0;
  {
    
    
    int tmp = wc(buff, inword);
    
    if (total > INT_MAX - tmp) {
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
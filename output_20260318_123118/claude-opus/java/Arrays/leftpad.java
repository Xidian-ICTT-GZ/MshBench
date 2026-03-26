public class LeftPad {

  /*@ 
    predicate chars(char[] a, int start, int length, list<char> cs) =
      0 <= start &*& start + length <= a.length &*&
      length == length && // to avoid unused warning
      chars_slice(a, start, length, cs);

    predicate chars_slice(char[] a, int start, int length, list<char> cs) =
      length == 0 ? emp :
      length > 0 :
        a[start] |-> ?v &*&
        chars_slice(a, start + 1, length - 1, ?cs1) &*&
        cs == cons(v, cs1);
  @*/

  /*@ requires s != null &*& chars(s, 0, s.length, ?cs); @*/
  /*@ ensures
        result != null &*&
        chars(result, 0, result.length, ?res)
        &*&
        res == append(rep(c, Math.max(n - s.length, 0)), cs);
  @*/
  static char[] leftPad(char c, int n, char[] s)
  {
    //@ chars(s, 0, s.length, ?cs0);
    int pad = Math.max(n - s.length, 0);
    char[] v = new char[pad + s.length];
    //@ chars(v, 0, v.length, ?csV0);
    int i = 0;

    //@ list<char> padList = rep(c, pad);
    //@ list<char> sList = cs0;
    //@ chars(v, 0, v.length, padList + sList);
    //@ chars_slice_predicate(v, 0, v.length, padList + sList);
    /*@
      loop_invariant 0 <= i &*& i <= pad &*&
        chars(v, 0, i, rep(c, i)) &*&
        chars(v, i, v.length - i, ?csRest) &*&
        csRest == rep(c, pad - i) + sList;
    @*/
    for(; ; i++)
    {
      if (i == pad) {
        break;
      }
      v[i] = c;
      //@ produce_chars_write(v, i, c);
    }

    /*@
      loop_invariant pad <= i &*& i <= v.length &*&
        chars(v, 0, pad, rep(c, pad)) &*&
        chars(v, pad, i - pad, take(i - pad, sList)) &*&
        chars(v, i, v.length - i, drop(i - pad, sList));
    @*/
    for(; ; i++)
    {
      if (i == v.length) {
        break;
      }
      v[i] = s[i - pad];
      //@ produce_chars_write(v, i, s[i - pad]);
    }
    
    //@ close chars(v, 0, v.length, rep(c, pad) + cs0);
    return v;
  }

  //@ predicate rep<char>(char c, int n) = n <= 0 ? nil : cons(c, rep(c, n - 1));

  //@ fixpoint list<char> rep(char c, int n) {
  //@   return n <= 0 ? nil : cons(c, rep(c, n - 1));
  //@ }

  //@ predicate chars_slice_predicate(char[] a, int start, int length, list<char> cs);

  //@ lemma void produce_chars_write(char[] a, int i, char c)
  //@ requires a[i] |-> ?v &*& chars_slice(a, 0, a.length, ?cs) &*& 0 <= i &*& i < a.length;
  //@ ensures a[i] |-> c &*& chars_slice(a, 0, a.length, update_list(cs, i, c));
  //@ {
  //@   open chars_slice(a, 0, a.length, cs);
  //@   switch(cs) {
  //@     case nil: return;
  //@     case cons(h, t):
  //@       if(i == 0) {
  //@         a[0] |-> _; close chars_slice(a, 0, a.length, update_list(cs, 0, c));
  //@       } else {
  //@         a[0] |-> h;
  //@         produce_chars_write(a + 1, i - 1, c);
  //@         close chars_slice(a, 0, a.length, update_list(cs, i, c));
  //@       }
  //@   }
  //@ }

  //@ fixpoint list<char> update_list(list<char> cs, int i, char c) {
  //@   switch(cs) {
  //@     case nil: return nil;
  //@     case cons(h, t): return i == 0 ? cons(c, t) : cons(h, update_list(t, i - 1, c));
  //@   }
  //@ }

  //@ fixpoint list<char> append(list<char> xs, list<char> ys) {
  //@   switch(xs) {
  //@     case nil: return ys;
  //@     case cons(x, xs0): return cons(x, append(xs0, ys));
  //@   }
  //@ }

  //@ fixpoint list<char> take(int n, list<char> xs) {
  //@   return n <= 0 ? nil : switch(xs) {
  //@     case nil: nil;
  //@     case cons(x, xs0): cons(x, take(n - 1, xs0));
  //@   };
  //@ }

  //@ fixpoint list<char> drop(int n, list<char> xs) {
  //@   return n <= 0 ? xs : switch(xs) {
  //@     case nil: nil;
  //@     case cons(x, xs0): drop(n - 1, xs0);
  //@   };
  //@ }

}
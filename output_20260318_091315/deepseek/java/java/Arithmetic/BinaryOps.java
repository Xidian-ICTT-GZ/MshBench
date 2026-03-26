import java.util.*;

public class BinaryOps
{
  //@ predicate valid() = true;
  
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
     int a = 60;   
     int b = 13;  
     int c = 0;
     //@ assert -2147483648 <= a &*& a <= 2147483647;
     //@ assert -2147483648 <= b &*& b <= 2147483647;
     //@ assert -2147483648 <= c &*& c <= 2147483647;

     c = a & b;
     //@ assert -2147483648 <= c &*& c <= 2147483647;

     c = a | b;
     //@ assert -2147483648 <= c &*& c <= 2147483647;

     c = a ^ b;
     //@ assert -2147483648 <= c &*& c <= 2147483647;

     c = ~a;
     //@ assert -2147483648 <= c &*& c <= 2147483647;

     c = a << 2;
     //@ assert -2147483648 <= c &*& c <= 2147483647;

     c = a >> 2;
     //@ assert -2147483648 <= c &*& c <= 2147483647;
  }
}
import java.util.*;

public class BinaryOps
{
  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
    
    
  {
     int a = 60;   
     int b = 13;  
     int c = 0;

     c = a & b;
     c = a | b;
     c = a ^ b;
     c = ~a;
     c = a << 2;
     c = a >> 2;
  }
}
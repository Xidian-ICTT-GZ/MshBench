import java.io.*;
import java.util.*;

class Program {
    /*@ 
    predicate list_elements(List list; int n) =
        n == 0 ? list.size() == 0 :
        list.size() == n &*&
        forall (int i; 0 <= i &*& i < n; list.get(i) != null);
    @*/

    //@ requires reader != null &*& list != null &*& list_elements(list, 0);
    //@ ensures list_elements(list, old(list.size()) + result);
    static void readLinesIntoList(BufferedReader reader, List list)
    {
        /*@ 
        int count = 0;
        @*/
        boolean repeat = true;
        do
        /*@ loop_invariant
              list_elements(list, count) &*&
              count >= 0;
          @*/
        {
            String line = reader.readLine();
            if (line == null)
                repeat = false;
            else {
                list.add(line);
                /*@ count++; @*/
            }
        }
        while (repeat);
        /*@ 
        result = list.size() - old(list.size());
        @*/
    }
}
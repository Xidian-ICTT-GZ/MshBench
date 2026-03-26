import java.io.*;
import java.util.*;

class Program {
    /*@ 
    predicate list_appendable(List list) = true;

    @*/

    static void readLinesIntoList(BufferedReader reader, List list)
    //@ requires reader != null &*& list != null &*& true;
    //@ ensures true;
    {
        boolean repeat = true;
        do
        //@ invariant reader != null &*& list != null &*& true &*& (repeat == true || repeat == false);
        {
            String line = reader.readLine();
            if (line == null)
                repeat = false;
            else
                list.add(line);
        }
        while (repeat);
    }
}
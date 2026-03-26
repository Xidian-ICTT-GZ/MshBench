import java.io.*;
import java.util.*;

class Program {
    //@ predicate list(List l) = l != null;
    
    static void readLinesIntoList(BufferedReader reader, List list)
        //@ requires reader != null &*& list(list);
        //@ ensures list(list);
    {
        boolean repeat = true;
        //@ close list(list);
        do
            //@ invariant list(list);
        {
            String line = reader.readLine();
            if (line == null)
                repeat = false;
            else
                //@ open list(list);
                list.add(line);
                //@ close list(list);
        }
        while (repeat);
    }
}
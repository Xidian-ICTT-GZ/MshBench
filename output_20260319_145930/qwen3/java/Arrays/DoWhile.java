import java.io.*;
import java.util.*;

class Program {
    /*@
    predicate BufferedReader(BufferedReader r) = true;
    predicate List(List l) = true;
    @*/

    //@ requires BufferedReader(reader) &*& List(list);
    //@ ensures BufferedReader(reader) &*& List(list);
    static void readLinesIntoList(BufferedReader reader, List list)
        
        
    {
        boolean repeat = true;
        do
            
        {
            //@ open BufferedReader(reader);
            String line = reader.readLine();
            //@ close BufferedReader(reader);
            if (line == null)
                repeat = false;
            else {
                //@ open List(list);
                list.add(line);
                //@ close List(list);
            }
        }
        //@ invariant BufferedReader(reader) &*& List(list);
        while (repeat);
    }
}
import java.io.*;
import java.util.*;

class Program {
    /*@
    predicate Program_dummy() = true;
    @*/
    static void readLinesIntoList(BufferedReader reader, List list)
        
        
    //@ requires true;
    //@ ensures true;
    {
        boolean repeat = true;
        do
            
        //@ invariant true;
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
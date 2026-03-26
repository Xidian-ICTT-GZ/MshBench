import java.io.*;
import java.util.*;

class Program {
    //@ requires reader != null &*& list != null;
    //@ ensures true;
    static void readLinesIntoList(BufferedReader reader, List list)
        
        
    {
        //@ close readerPred(reader);
        boolean repeat = true;
        //@ loop_invariant repeat == true || repeat == false;
        do
            
        {
            //@ open readerPred(reader);
            String line = reader.readLine();
            if (line == null)
                repeat = false;
            else
                list.add(line);
            //@ close readerPred(reader);
        }
        while (repeat);
    }
    
    /*@
    predicate readerPred(BufferedReader r) = true;
    @*/
}
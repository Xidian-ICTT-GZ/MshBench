import java.io.*;
import java.util.*;

class Program {
    static void readLinesIntoList(BufferedReader reader, List list)
        
        
    //@ requires reader.Reader() &*& list != null;
    //@ ensures reader.Reader() &*& list != null;
    {
        boolean repeat = true;
        do
            
        //@ invariant reader.Reader() &*& list != null;
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
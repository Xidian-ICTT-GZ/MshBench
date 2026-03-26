import java.io.*;
import java.util.*;

class Program {
    //@ requires reader != null;
    //@ requires list != null;
    //@ ensures true;
    static void readLinesIntoList(BufferedReader reader, List list)
        
        
    {
        boolean repeat = true;
        //@ loop_invariant true;
        do
            
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
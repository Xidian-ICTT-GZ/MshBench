import java.io.*;
import java.util.*;

class Program {
    //@ requires true;
    //@ ensures true;
    static void readLinesIntoList(BufferedReader reader, List list)
        
        
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
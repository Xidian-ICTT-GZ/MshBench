import java.io.*;
import java.util.*;

class Program {
    //@ requires reader != null &*& list != null;
    //@ ensures true;
    static void readLinesIntoList(BufferedReader reader, List list)
        
        
    {
        boolean repeat = true;
        //@ close exists(reader);
        //@ close exists(list);
        do
            
        {
            //@ open exists(reader);
            //@ open exists(list);
            String line = reader.readLine();
            if (line == null)
                repeat = false;
            else
                list.add(line);
            //@ close exists(reader);
            //@ close exists(list);
        }
        while (repeat);
    }
}
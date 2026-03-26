import java.io.*;
import java.util.*;

/*@

predicate program() = true;

@*/

class Program {
    //@ requires reader != null &*& list != null;
    //@ ensures true;
    static void readLinesIntoList(BufferedReader reader, List list)
        throws IOException
    {
        boolean repeat = true;
        do
        //@ invariant reader != null &*& list != null;
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
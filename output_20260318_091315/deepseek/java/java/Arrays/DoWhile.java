import java.io.*;
import java.util.*;

class Program {
    //@ predicate BufferedReaderState(BufferedReader br) = br != null;
    //@ predicate ListState(List l) = l != null;
    
    static void readLinesIntoList(BufferedReader reader, List list)
    //@ requires BufferedReaderState(reader) &*& ListState(list);
    //@ ensures BufferedReaderState(reader) &*& ListState(list);
    {
        boolean repeat = true;
        //@ loop_invariant repeat == true || repeat == false;
        //@ loop_invariant BufferedReaderState(reader) &*& ListState(list);
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
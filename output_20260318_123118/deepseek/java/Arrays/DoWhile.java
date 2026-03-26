import java.io.*;
import java.util.*;

class Program {
    //@ predicate BufferedReaderState(BufferedReader br) = br != null;
    //@ predicate ListState(List l) = l != null;
    //@ predicate ListStateWithSize(List l, int size) = l != null &*& size >= 0;

    static void readLinesIntoList(BufferedReader reader, List list)
    //@ requires BufferedReaderState(reader) &*& ListState(list);
    //@ ensures BufferedReaderState(reader) &*& ListState(list);
    {
        boolean repeat = true;
        //@ close ListStateWithSize(list, 0);
        do
        //@ invariant BufferedReaderState(reader) &*& ListStateWithSize(list, _);
        {
            String line = reader.readLine();
            if (line == null)
                repeat = false;
            else
                //@ open ListStateWithSize(list, ?size);
                //@ close ListStateWithSize(list, size);
                list.add(line);
        }
        while (repeat);
        //@ open ListStateWithSize(list, _);
    }
}
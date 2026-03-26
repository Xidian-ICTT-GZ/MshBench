import java.io.*;
import java.util.*;

class Program {
    static void readLinesIntoList(BufferedReader reader, List list)
    //@ requires reader != null &*& list != null &*& java.io.Reader.Reader(reader);
    //@ ensures java.io.Reader.Reader(reader);
    {
        boolean repeat = true;
        do
        //@ invariant true &*& java.io.Reader.Reader(reader);
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
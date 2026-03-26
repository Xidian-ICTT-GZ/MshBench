import java.io.*;
import java.util.*;

class Program {
    static void readLinesIntoList(BufferedReader reader, List list)
        //@ requires reader != null &*& list != null;
        //@ ensures true;
    {
        boolean repeat = true;
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
import java.io.*;
import java.util.*;

class Program {
    /*@
    predicate BufferedReader_valid(BufferedReader reader) = true;
    predicate List_valid(List list) = true;
    @*/

    static void readLinesIntoList(BufferedReader reader, List list)
    //@ requires BufferedReader_valid(reader) &*& List_valid(list);
    //@ ensures BufferedReader_valid(reader) &*& List_valid(list);
    {
        boolean repeat = true;
        do
        //@ invariant BufferedReader_valid(reader) &*& List_valid(list);
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
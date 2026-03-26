import java.io.*;
import java.util.*;

/*@
predicate BufferedReaderP(BufferedReader r;) = r != null;

predicate ListP(List l;) = l != null;
@*/

class Program {
    static void readLinesIntoList(BufferedReader reader, List list)
        //@ requires BufferedReaderP(reader) &*& ListP(list);
        //@ ensures BufferedReaderP(reader) &*& ListP(list);
    {
        boolean repeat = true;
        do
            //@ invariant BufferedReaderP(reader) &*& ListP(list);
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
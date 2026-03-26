import java.io.*;
import java.util.*;

/*@ predicate BufferedReader_valid(BufferedReader r) = true; @*/
/*@ predicate List_valid(List l) = true; @*/

class Program {
    //@ requires reader != null &*& list != null &*& BufferedReader_valid(reader) &*& List_valid(list);
    //@ ensures BufferedReader_valid(reader) &*& List_valid(list);
    static void readLinesIntoList(BufferedReader reader, List list)
        
        
    {
        boolean repeat = true;
        //@ invariant reader != null &*& list != null &*& BufferedReader_valid(reader) &*& List_valid(list) &*& repeat == (true || false);
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
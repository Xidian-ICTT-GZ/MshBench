package iterator;

interface Iterator {

    
    
    boolean hasNext();
        
        

    Object next();
        
        

}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    

    
    public SingletonIterator(Object value)
        //@ requires true;
        //@ ensures this.value |-> value &*& this.done |-> false;
    {
        this.value = value;
        this.done = false;
        
    }
    
    public boolean hasNext()
        //@ requires this.done |-> ?d;
        //@ ensures this.done |-> d &*& result == !d;
    {
        
        return !done;
        
    }
    
    public Object next()
        //@ requires this.value |-> ?v &*& this.done |-> false;
        //@ ensures this.value |-> v &*& this.done |-> true &*& result == v;
    {
        
        done = true;
        return value;
        
    }

}

class IteratorUtil {

    public static Object getLast(Iterator iterator)
        //@ requires iterator != null &*& iterator.hasNext() |-> true;
        //@ ensures iterator.hasNext() |-> false &*& result != null;
    {
        Object value = null;
        boolean more = iterator.hasNext();
        while (more)
            //@ invariant iterator != null &*& iterator.hasNext() |-> more &*& value != null || !more;
        {
            
            value = iterator.next();
            more = iterator.hasNext();
        }
        return value;
    }

}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Object o = new Object();
        SingletonIterator i = new SingletonIterator(o);
        boolean before = i.hasNext();
        assert(before);

        Object last = IteratorUtil.getLast(i);
        assert last == o;
      
        boolean after = i.hasNext();
        assert(!after);
    }

}
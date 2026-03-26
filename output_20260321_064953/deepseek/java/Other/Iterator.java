package iterator;

interface Iterator {

    
    
    boolean hasNext();
        
        

    Object next();
        
        

}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    //@ predicate valid() = value |-> ?v &*& done |-> ?d;

    

    
    public SingletonIterator(Object value)
        //@ requires true;
        //@ ensures valid();
    {
        this.value = value;
        this.done = false;
        //@ close valid();
    }
    
    public boolean hasNext()
        //@ requires valid();
        //@ ensures valid() &*& result == !done;
    {
        //@ open valid();
        return !done;
        //@ close valid();
    }
    
    public Object next()
        //@ requires valid() &*& !done;
        //@ ensures valid() &*& done |-> true &*& result == value;
    {
        //@ open valid();
        done = true;
        //@ close valid();
        return value;
    }

}

class IteratorUtil {

    public static Object getLast(Iterator iterator)
        //@ requires iterator.valid();
        //@ ensures iterator.valid();
    {
        Object value = null;
        boolean more = iterator.hasNext();
        while (more)
            //@ invariant iterator.valid();
        {
            //@ open iterator.valid();
            //@ close iterator.valid();
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
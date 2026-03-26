package iterator;

interface Iterator {
    //@ predicate valid() = true;
    
    boolean hasNext();
    //@ requires valid();
    //@ ensures valid();
        
    Object next();
    //@ requires valid();
    //@ ensures valid();
}

class SingletonIterator implements Iterator {
    Object value;
    boolean done;

    //@ predicate valid() = value |-> ?v &*& done |-> ?d;

    public SingletonIterator(Object value)
    //@ requires true;
    //@ ensures valid() &*& done |-> false;
    {
        this.value = value;
        this.done = false;
        //@ close valid();
    }
    
    public boolean hasNext()
    //@ requires valid();
    //@ ensures valid();
    {
        //@ open valid();
        boolean result = !done;
        //@ close valid();
        return result;
    }
    
    public Object next()
    //@ requires valid();
    //@ ensures valid();
    {
        //@ open valid();
        done = true;
        Object result = value;
        //@ close valid();
        return result;
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
package iterator;

interface Iterator {

    //@ requires true;
    boolean hasNext();
        
    //@ requires true;
    Object next();
        
}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    /*@
    predicate valid() =
        value |-> ?v &*& done |-> ?d;
    @*/

    //@ requires true;
    public SingletonIterator(Object value)
    {
        this.value = value;
        this.done = false;
        //@ close valid();
    }
    
    //@ requires valid();
    //@ ensures valid() &*& result == !done;
    public boolean hasNext()
    {
        //@ open valid();
        boolean r = !done;
        //@ close valid();
        return r;
    }
    
    //@ requires valid() &*& !done;
    //@ ensures valid() &*& done &*& result == this.value;
    public Object next()
    {
        //@ open valid();
        done = true;
        Object r = value;
        //@ close valid();
        return r;
    }

}

class IteratorUtil {

    //@ requires true;
    public static Object getLast(Iterator iterator)
    {
        Object value = null;
        boolean more = iterator.hasNext();
        //@ invariant true;
        while (more)
        {
            value = iterator.next();
            more = iterator.hasNext();
        }
        return value;
    }

}

class Program {

    //@ requires true;
    public static void main(String[] args)
    {
        Object o = new Object();
        SingletonIterator i = new SingletonIterator(o);
        //@ open i.valid();
        boolean before = !i.done;
        //@ close i.valid();
        assert(before);

        Object last = IteratorUtil.getLast(i);
        assert last == o;
      
        //@ open i.valid();
        boolean after = i.done;
        //@ close i.valid();
        assert(!after);
    }

}
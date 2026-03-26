package iterator;

interface Iterator {

    //@ requires true;
    //@ ensures true;
    boolean hasNext();
        
    //@ requires true;
    //@ ensures true;
    Object next();
        
}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    /*@ predicate valid() =
          this.done |-> ?d &*& this.value |-> ?v &*&
          (d == false ? emp : emp);
    @*/

    //@ requires value != null;
    //@ ensures valid() &*& result == this;
    public SingletonIterator(Object value)
    {
        this.value = value;
        this.done = false;
    }
    
    //@ requires valid();
    //@ ensures valid() &*& result == !done;
    public boolean hasNext()
    {
        return !done;
    }
    
    //@ requires valid() &*& !done;
    //@ ensures valid() &*& done &*& result == this.value;
    public Object next()
    {
        done = true;
        return value;
    }

}

class IteratorUtil {

    //@ requires true;
    //@ ensures true;
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
    //@ ensures true;
    public static void main(String[] args)
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
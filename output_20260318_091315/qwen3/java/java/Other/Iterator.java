package iterator;

interface Iterator {

    //@ requires true;
    //@ ensures true;
    boolean hasNext();
        
    //@ requires this.done |-> ?d &*& d == false;
    //@ ensures this.done |-> true &*& result == this.value |-> ?v &*& v == old(this.value);
    Object next();
        
}

/*@ predicate SingletonIterator(Object iter, Object value, boolean done) =
    iter |-> ?o &*& o..value |-> value &*& o..done |-> done;
@*/

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    //@ requires true;
    //@ ensures SingletonIterator(this, value, false);
    public SingletonIterator(Object value)
    {
        this.value = value;
        this.done = false;
    }
    
    //@ requires SingletonIterator(this, ?v, ?d);
    //@ ensures SingletonIterator(this, v, d) &*& result == !d;
    public boolean hasNext()
    {
        return !done;
    }
    
    //@ requires SingletonIterator(this, ?v, false);
    //@ ensures SingletonIterator(this, v, true) &*& result == v;
    public Object next()
    {
        done = true;
        return value;
    }

}

class IteratorUtil {

    //@ requires exists(?iter) &*& SingletonIterator(iter, ?v, false);
    //@ ensures SingletonIterator(iter, v, true) &*& result == v;
    public static Object getLast(Iterator iterator)
    {
        Object value = null;
        boolean more = iterator.hasNext();
        //@ loop_invariant exists(?iter) &*& SingletonIterator(iter, ?v, ?d) &*& (d ? value == v : value == null) &*& more == !d;
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
package iterator;

/*@
predicate IteratorState(Iterator i; boolean hasMore, Object val) =
    i.getClass() == SingletonIterator.class &*&
    ((SingletonIterator)i).value |-> val &*&
    ((SingletonIterator)i).done |-> ?d &*&
    hasMore == !d;
@*/

interface Iterator {

    //@ predicate valid(boolean hasMore, Object val);
    
    boolean hasNext();
        //@ requires valid(?hasMore, ?val);
        //@ ensures valid(hasMore, val) &*& result == hasMore;

    Object next();
        //@ requires valid(true, ?val);
        //@ ensures valid(false, val) &*& result == val;

}

/*@
predicate SingletonIteratorInv(SingletonIterator i; boolean hasMore, Object val) =
    i.value |-> val &*& i.done |-> ?d &*& hasMore == !d;
@*/

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    //@ predicate valid(boolean hasMore, Object val) = SingletonIteratorInv(this, hasMore, val);

    
    public SingletonIterator(Object value)
        //@ requires true;
        //@ ensures valid(true, value);
    {
        this.value = value;
        this.done = false;
        //@ close SingletonIteratorInv(this, true, value);
        //@ close valid(true, value);
    }
    
    public boolean hasNext()
        //@ requires valid(?hasMore, ?val);
        //@ ensures valid(hasMore, val) &*& result == hasMore;
    {
        //@ open valid(hasMore, val);
        //@ open SingletonIteratorInv(this, hasMore, val);
        boolean result = !done;
        //@ close SingletonIteratorInv(this, hasMore, val);
        //@ close valid(hasMore, val);
        return result;
    }
    
    public Object next()
        //@ requires valid(true, ?val);
        //@ ensures valid(false, val) &*& result == val;
    {
        //@ open valid(true, val);
        //@ open SingletonIteratorInv(this, true, val);
        done = true;
        Object result = value;
        //@ close SingletonIteratorInv(this, false, val);
        //@ close valid(false, val);
        return result;
    }

}

class IteratorUtil {

    public static Object getLast(Iterator iterator)
        //@ requires iterator.valid(true, ?v);
        //@ ensures iterator.valid(false, v) &*& result == v;
    {
        Object value = null;
        boolean more = iterator.hasNext();
        while (more)
            //@ invariant more == true &*& iterator.valid(true, v) || more == false &*& iterator.valid(false, v) &*& value == v;
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
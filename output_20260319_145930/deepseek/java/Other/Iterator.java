package iterator;

interface Iterator {
    //@ predicate IteratorState() = true;
    
    boolean hasNext();
    //@ requires IteratorState();
    //@ ensures IteratorState();
        
    Object next();
    //@ requires IteratorState();
    //@ ensures IteratorState();
}

class SingletonIterator implements Iterator {
    Object value;
    boolean done;
    
    //@ predicate IteratorState() = SingletonIterator(this, ?v, ?d) &*& d == done &*& v == value;
    //@ predicate SingletonIterator(Object v, boolean d) = this.value |-> v &*& this.done |-> d;
    
    public SingletonIterator(Object value)
    //@ requires true;
    //@ ensures SingletonIterator(this, value, false);
    {
        this.value = value;
        this.done = false;
        //@ close SingletonIterator(this, value, false);
        //@ close IteratorState();
    }
    
    public boolean hasNext()
    //@ requires IteratorState();
    //@ ensures IteratorState();
    {
        //@ open IteratorState();
        //@ open SingletonIterator(this, ?v, ?d);
        boolean result = !done;
        //@ close SingletonIterator(this, v, d);
        //@ close IteratorState();
        return result;
    }
    
    public Object next()
    //@ requires IteratorState();
    //@ ensures IteratorState();
    {
        //@ open IteratorState();
        //@ open SingletonIterator(this, ?v, ?d);
        done = true;
        Object result = value;
        //@ close SingletonIterator(this, v, true);
        //@ close IteratorState();
        return result;
    }
}

class IteratorUtil {
    public static Object getLast(Iterator iterator)
    //@ requires iterator.IteratorState();
    //@ ensures iterator.IteratorState();
    {
        Object value = null;
        boolean more = iterator.hasNext();
        //@ close more == true ? iterator.IteratorState() : iterator.IteratorState();
        while (more)
        //@ invariant iterator.IteratorState();
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
        //@ open i.SingletonIterator(o, false);
        //@ close i.IteratorState();
        boolean before = i.hasNext();
        //@ assert before == true;
        assert(before);

        Object last = IteratorUtil.getLast(i);
        //@ assert last == o;
      
        boolean after = i.hasNext();
        //@ assert after == false;
        assert(!after);
        //@ open i.IteratorState();
        //@ open i.SingletonIterator(o, true);
    }
}
package iterator;

/*@
predicate SingletonIterator_inv(SingletonIterator this) = 
    this->value |-> ?v &*& this->done |-> ?d;
@*/

interface Iterator {

    //@ requires true;
    //@ ensures result == true || result == false;
    boolean hasNext();

    //@ requires true;
    //@ ensures true;
    Object next();

}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    /*@ public instance invariant SingletonIterator_inv(this); @*/

    //@ requires true;
    //@ ensures SingletonIterator_inv(this);
    public SingletonIterator(Object value)
    {
        this.value = value;
        this.done = false;
    }
    
    //@ requires SingletonIterator_inv(this);
    //@ ensures SingletonIterator_inv(this) &*& result == !this.done;
    public boolean hasNext()
    {
        //@ open SingletonIterator_inv(this);
        //@ assert this->done |-> ?d;
        return !done;
        //@ close SingletonIterator_inv(this);
    }
    
    //@ requires SingletonIterator_inv(this);
    //@ ensures SingletonIterator_inv(this);
    public Object next()
    {
        //@ open SingletonIterator_inv(this);
        done = true;
        //@ close SingletonIterator_inv(this);
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
        //@ open true;
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
package iterator;

/*@
predicate SingletonIterator_p(SingletonIterator this, Object value, boolean done) =
  this.value |-> value &*& this.done |-> done;
@*/

interface Iterator {
    boolean hasNext();
    Object next();
}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    /*@ invariant SingletonIterator_p(this, value, done); @*/

    public SingletonIterator(Object value)
        //@ requires true;
        //@ ensures SingletonIterator_p(this, value, false);
    {
        this.value = value;
        this.done = false;
    }

    public boolean hasNext()
        //@ requires SingletonIterator_p(this, ?v, ?d);
        //@ ensures SingletonIterator_p(this, v, d) &*& result == !d;
    {
        //@ open SingletonIterator_p(this, value, done);
        boolean res = !done;
        //@ close SingletonIterator_p(this, value, done);
        return res;
    }

    public Object next()
        //@ requires SingletonIterator_p(this, ?v, false);
        //@ ensures SingletonIterator_p(this, v, true) &*& result == v;
    {
        //@ open SingletonIterator_p(this, value, false);
        done = true;
        Object ret = value;
        //@ close SingletonIterator_p(this, value, true);
        return ret;
    }
}

class IteratorUtil {

    public static Object getLast(Iterator iterator)
        //@ requires true;
        //@ ensures true;
    {
        Object value = null;
        boolean more = iterator.hasNext();
        //@ while(more)
        //@     invariant true;
        while (more)
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
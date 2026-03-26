package iterator;

/*@
predicate SingletonIterator_pred(SingletonIterator this;) =
  this.value |-> _ &*& this.done |-> _;
@*/

interface Iterator {

    //@ requires true;
    //@ ensures result == true || result == false;
    boolean hasNext();

    //@ requires true;
    //@ ensures result != null;
    Object next();

}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    //@ requires value != null;
    //@ ensures SingletonIterator_pred(this);
    public SingletonIterator(Object value)
    {
        this.value = value;
        this.done = false;
    }

    //@ requires SingletonIterator_pred(this);
    //@ ensures SingletonIterator_pred(this) &*& result == !this.done;
    public boolean hasNext()
    {
        return !done;
    }

    //@ requires SingletonIterator_pred(this);
    //@ ensures SingletonIterator_pred(this) &*& result == this.value;
    public Object next()
    {
        done = true;
        return value;
    }

}

class IteratorUtil {

    //@ requires iterator != null;
    //@ ensures true;
    public static Object getLast(Iterator iterator)
    {
        Object value = null;
        boolean more = iterator.hasNext();
        //@ // loop invariant more == iterator.hasNext();
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
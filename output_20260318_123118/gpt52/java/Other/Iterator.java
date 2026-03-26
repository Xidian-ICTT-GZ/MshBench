package iterator;

interface Iterator {

    //@ predicate iterator_state(boolean hasNext, Object last);

    //@ requires iterator_state(?hn, ?last);
    //@ ensures iterator_state(result, last);

    boolean hasNext();

    //@ requires iterator_state(true, ?last);
    //@ ensures iterator_state(false, result);

    Object next();

}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    /*@ predicate iterator_state(boolean hasNext, Object last) =
            this.value |-> ?v &*& this.done |-> ?d &*& last == v &*& hasNext == !d;
    @*/

    public SingletonIterator(Object value)
    //@ requires true;
    //@ ensures iterator_state(true, value);
    {
        this.value = value;
        this.done = false;

    }

    public boolean hasNext()
    //@ requires iterator_state(?hn, ?last);
    //@ ensures iterator_state(result, last);
    {

        return !done;

    }

    public Object next()
    //@ requires iterator_state(true, ?last);
    //@ ensures iterator_state(false, result);
    {

        done = true;
        return value;

    }

}

class IteratorUtil {

    public static Object getLast(Iterator iterator)
    //@ requires iterator != null &*& iterator.iterator_state(?hn, ?last);
    //@ ensures iterator.iterator_state(false, last) &*& result == last;
    {
        Object value = null;
        boolean more = iterator.hasNext();
        //@ assert iterator.iterator_state(more, last);
        while (more)

        //@ invariant iterator.iterator_state(more, last) &*& value == last;
        {

            value = iterator.next();
            //@ assert iterator.iterator_state(false, value);
            more = iterator.hasNext();
            //@ assert iterator.iterator_state(more, value);
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
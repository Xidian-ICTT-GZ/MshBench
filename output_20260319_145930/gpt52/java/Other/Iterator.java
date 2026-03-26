package iterator;

interface Iterator {

    //@ predicate iter() = true;

    //@ requires iter();
    //@ ensures iter();
    boolean hasNext();

    //@ requires iter();
    //@ ensures iter();
    Object next();

}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    /*@ predicate iter() =
            this.value |-> ?v &*& this.done |-> ?d;
    @*/

    //@ requires true;
    //@ ensures iter();
    public SingletonIterator(Object value)
    //@ requires true;
    //@ ensures iter();
    {
        this.value = value;
        this.done = false;
        //@ close iter();
    }

    //@ requires iter();
    //@ ensures iter();
    public boolean hasNext()
    {
        //@ open iter();
        boolean r = !done;
        //@ close iter();
        return r;
    }

    //@ requires iter();
    //@ ensures iter();
    public Object next()
    {
        //@ open iter();
        done = true;
        Object r = value;
        //@ close iter();
        return r;
    }

}

class IteratorUtil {

    //@ requires iterator.iter();
    //@ ensures iterator.iter();
    public static Object getLast(Iterator iterator)
    {
        Object value = null;
        boolean more = iterator.hasNext();
        while (more)
            //@ invariant iterator.iter();
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
        //@ open i.iter();
        boolean before = !i.done;
        //@ close i.iter();
        assert(before);

        Object last = IteratorUtil.getLast(i);
        //@ open i.iter();
        Object v = i.value;
        //@ close i.iter();
        assert last == v;

        boolean after = i.hasNext();
        assert(!after);
    }

}
package iterator;

interface Iterator {
    //@ predicate iterator_state(boolean hasMore, Object current);

    //@ requires this.iterator_state(?h, ?c);
    //@ ensures this.iterator_state(h, c) &*& result == h;
    boolean hasNext();

    //@ requires this.iterator_state(true, ?c);
    //@ ensures this.iterator_state(false, c) &*& result == c;
    Object next();
}

class SingletonIterator implements Iterator {
    Object value;
    boolean done;

    /*@ 
    predicate singletonIterator(this obj;) =
      obj.value |-> ?v &*& obj.done |-> ?d;

    predicate iterator_state(boolean hasMore, Object current) =
      singletonIterator(this) &*&
      hasMore == !done &*&
      current == value;
    @*/

    //@ requires value != null;
    //@ ensures singletonIterator(this) &*& !done &*& value == this.value;
    public SingletonIterator(Object value)
    {
        this.value = value;
        this.done = false;
    }

    //@ requires singletonIterator(this);
    //@ ensures singletonIterator(this) &*& result == !done;
    public boolean hasNext()
    {
        return !done;
    }

    //@ requires singletonIterator(this) &*& !done;
    //@ ensures singletonIterator(this) &*& done &*& result == value;
    public Object next()
    {
        done = true;
        return value;
    }
}

class IteratorUtil {
    //@ predicate iterator_state(Iterator iter, boolean hasMore, Object current) =
    //@     iter.iterator_state(hasMore, current);

    /*@
    lemma void update_hasNext(Iterator iter, boolean h0, Object c)
        requires iter.iterator_state(h0, c);
        ensures iter.iterator_state(h0, c);
    {
        // noop lemma for framing
    }
    @*/

    //@ requires iterator.iterator_state(?h, ?c);
    //@ ensures iterator.iterator_state(false, ?last) &*& result == last;
    public static Object getLast(Iterator iterator)
    {
        Object value = null;
        boolean more = iterator.hasNext();

        //@ open iterator.iterator_state(more, ?cur);
        //@ object more0 = more;
        while (more)
            //@ invariant iterator.iterator_state(more, value);
        {
            value = iterator.next();
            more = iterator.hasNext();
            //@ open iterator.iterator_state(more, ?cur2);
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
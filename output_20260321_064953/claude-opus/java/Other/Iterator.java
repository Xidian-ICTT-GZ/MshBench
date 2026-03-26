package iterator;

/*@
predicate Iterator(Iterator i;) =
    i != null;

predicate SingletonIteratorInv(SingletonIterator i; Object v, boolean d) =
    i.value |-> v &*& i.done |-> d;
@*/

interface Iterator {

    //@ requires Iterator(this);
    //@ ensures true;
    boolean hasNext();
        
        

    //@ requires Iterator(this);
    //@ ensures true;
    Object next();
        
        

}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    /*@
    predicate Iterator() = SingletonIteratorInv(this, _, _);
    @*/

    
    public SingletonIterator(Object value)
        //@ requires true;
        //@ ensures SingletonIteratorInv(this, value, false);
    {
        this.value = value;
        this.done = false;
        //@ close SingletonIteratorInv(this, value, false);
    }
    
    public boolean hasNext()
        //@ requires SingletonIteratorInv(this, ?v, ?d);
        //@ ensures SingletonIteratorInv(this, v, d) &*& result == !d;
    {
        //@ open SingletonIteratorInv(this, v, d);
        boolean r = !done;
        //@ close SingletonIteratorInv(this, v, d);
        return r;
    }
    
    public Object next()
        //@ requires SingletonIteratorInv(this, ?v, ?d);
        //@ ensures SingletonIteratorInv(this, v, true) &*& result == v;
    {
        //@ open SingletonIteratorInv(this, v, d);
        done = true;
        Object r = value;
        //@ close SingletonIteratorInv(this, v, true);
        return r;
    }

}

class IteratorUtil {

    public static Object getLast(SingletonIterator iterator)
        //@ requires SingletonIteratorInv(iterator, ?v, ?d);
        //@ ensures SingletonIteratorInv(iterator, v, true) &*& (d ? result == null : result == v);
    {
        Object value = null;
        boolean more = iterator.hasNext();
        while (more)
            //@ invariant SingletonIteratorInv(iterator, v, ?d2) &*& (more ? !d2 : true) &*& (d2 ? value == v : value == null);
        {
            //@ open SingletonIteratorInv(iterator, v, d2);
            //@ close SingletonIteratorInv(iterator, v, d2);
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
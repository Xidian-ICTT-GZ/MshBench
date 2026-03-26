package iterator;

//@ predicate Iterator(Iterator it;) = true;

interface Iterator {
    
    
    boolean hasNext();
    //@ requires Iterator(this);
    //@ ensures Iterator(this);
        
        

    Object next();
    //@ requires Iterator(this);
    //@ ensures Iterator(this);
        
        

}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    //@ predicate SingletonIterator(Object v, boolean d) = this.value |-> v &*& this.done |-> d;

    

    
    public SingletonIterator(Object value)
        //@ requires true;
        //@ ensures SingletonIterator(value, false);
    {
        this.value = value;
        this.done = false;
        //@ close SingletonIterator(value, false);
    }
    
    public boolean hasNext()
        //@ requires SingletonIterator(?v, ?d);
        //@ ensures SingletonIterator(v, d) &*& result == !d;
    {
        //@ open SingletonIterator(v, d);
        boolean result = !done;
        //@ close SingletonIterator(v, d);
        return result;
    }
    
    public Object next()
        //@ requires SingletonIterator(?v, false);
        //@ ensures SingletonIterator(v, true) &*& result == v;
    {
        //@ open SingletonIterator(v, false);
        done = true;
        //@ close SingletonIterator(v, true);
        return value;
    }

    //@ lemma void closeIterator();
    //@ requires SingletonIterator(_, _);
    //@ ensures Iterator(this);
    //@ { close Iterator(this); }

}

class IteratorUtil {

    public static Object getLast(Iterator iterator)
        //@ requires Iterator(iterator);
        //@ ensures Iterator(iterator);
    {
        Object value = null;
        //@ open Iterator(iterator);
        //@ iterator.closeIterator();
        boolean more = iterator.hasNext();
        while (more)
            //@ invariant Iterator(iterator);
        {
            //@ open Iterator(iterator);
            //@ iterator.closeIterator();
            value = iterator.next();
            //@ open Iterator(iterator);
            //@ iterator.closeIterator();
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
        //@ assert before == true;
        assert(before);

        //@ i.closeIterator();
        Object last = IteratorUtil.getLast(i);
        //@ open Iterator(i);
        //@ i.closeIterator();
        //@ assert last == o;
        assert last == o;
      
        boolean after = i.hasNext();
        //@ assert after == false;
        assert(!after);
        //@ open SingletonIterator(o, true);
    }

}
package iterator;

interface Iterator {

    
    
    //@ requires true;
    //@ ensures true;
    boolean hasNext();
        
        

    //@ requires true;
    //@ ensures true;
    Object next();
        
        

}

/*@
predicate singletonIterator(SingletonIterator it; Object v, boolean d) =
    it.value |-> v &*& it.done |-> d;
@*/

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    

    
    //@ requires true;
    //@ ensures singletonIterator(this, value, false);
    public SingletonIterator(Object value)
        
        
    {
        this.value = value;
        this.done = false;
        
    }
    
    //@ requires singletonIterator(this, ?v, ?d);
    //@ ensures singletonIterator(this, v, d) &*& result == !d;
    public boolean hasNext()
        
        
    {
        
        return !done;
        
    }
    
    //@ requires singletonIterator(this, ?v, ?d);
    //@ ensures singletonIterator(this, v, true) &*& result == v;
    public Object next()
        
        
    {
        
        done = true;
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
        while (more)
            //@ invariant true;
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
        //@ close singletonIterator(?it, ?v, ?d);
        SingletonIterator i = new SingletonIterator(o);
        //@ open singletonIterator(i, o, false);
        boolean before = i.hasNext();
        assert(before);

        //@ open singletonIterator(i, o, false);
        Object last = IteratorUtil.getLast(i);
        assert last == o;
      
        //@ open singletonIterator(i, o, true);
        boolean after = i.hasNext();
        assert(!after);
        //@ close singletonIterator(i, o, true);
    }

}
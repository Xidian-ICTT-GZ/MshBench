package iterator;

interface Iterator {

    
    
    //@ requires true;
    //@ ensures true;
    boolean hasNext();
        
        

    //@ requires true;
    //@ ensures true;
    Object next();
        
        

}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    /*@
    predicate valid() = this.value |-> ?v &*& this.done |-> ?d;
    @*/

    

    
    //@ requires this.value |-> _ &*& this.done |-> _;
    //@ ensures valid();
    public SingletonIterator(Object value)
        
        
    {
        this.value = value;
        this.done = false;
        //@ close valid();
    }
    
    //@ requires valid();
    //@ ensures valid() &*& result == (!old(done));
    public boolean hasNext()
        
        
    {
        //@ open valid();
        boolean d = done;
        //@ close valid();
        return !d;
        
    }
    
    //@ requires valid();
    //@ ensures valid() &*& done == true &*& result == value;
    public Object next()
        
        
    {
        //@ open valid();
        done = true;
        Object v = value;
        //@ close valid();
        return v;
        
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

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
        
        
    {
        Object o = new Object();
        //@ close o != null ? emp : emp;
        //@ close emp;
        SingletonIterator i = new SingletonIterator(o);
        boolean before = i.hasNext();
        assert(before);

        Object last = IteratorUtil.getLast(i);
        assert last == o;
      
        boolean after = i.hasNext();
        assert(!after);
    }

}
package iterator;

interface Iterator {

    
    
    boolean hasNext();
        
        

    Object next();
        
        

}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    /*@
    predicate inv(Object v, boolean d) = this.value |-> v &*& this.done |-> d;
    @*/

    

    
    //@ requires true;
    //@ ensures inv(value, false);
    public SingletonIterator(Object value)
        
        
    {
        this.value = value;
        this.done = false;
        
        //@ close inv(value, false);
    }
    
    //@ requires inv(?v, ?d);
    //@ ensures inv(v, d) &*& result == !d;
    public boolean hasNext()
        
        
    {
        //@ open inv(?v, ?d);
        boolean res = !done;
        //@ close inv(v, d);
        return res;
        
    }
    
    //@ requires inv(?v, ?d);
    //@ ensures inv(v, true) &*& result == v;
    public Object next()
        
        
    {
        
        //@ open inv(?v, ?d);
        done = true;
        Object res = value;
        //@ close inv(v, true);
        return res;
        
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
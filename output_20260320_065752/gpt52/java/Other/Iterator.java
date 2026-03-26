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
predicate SingletonIterator_inv(SingletonIterator it; Object value, boolean done) =
    it.value |-> value &*& it.done |-> done;
@*/

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    

    
    //@ requires true;
    //@ ensures SingletonIterator_inv(this, value, false);
    public SingletonIterator(Object value)
        
        
    {
        this.value = value;
        this.done = false;
        
    }
    
    //@ requires SingletonIterator_inv(this, ?v, ?d);
    //@ ensures SingletonIterator_inv(this, v, d) &*& result == !d;
    public boolean hasNext()
        
        
    {
        //@ open SingletonIterator_inv(this, v, d);
        boolean res = !done;
        //@ close SingletonIterator_inv(this, v, d);
        return res;
        
    }
    
    //@ requires SingletonIterator_inv(this, ?v, ?d);
    //@ ensures SingletonIterator_inv(this, v, true) &*& result == v;
    public Object next()
        
        
    {
        //@ open SingletonIterator_inv(this, v, d);
        done = true;
        Object res = value;
        //@ close SingletonIterator_inv(this, v, true);
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
        SingletonIterator i = new SingletonIterator(o);
        //@ open SingletonIterator_inv(i, o, false);
        //@ close SingletonIterator_inv(i, o, false);
        boolean before = i.hasNext();
        assert(before);

        Object last = IteratorUtil.getLast(i);
        assert last == o;
      
        boolean after = i.hasNext();
        assert(!after);
    }

}
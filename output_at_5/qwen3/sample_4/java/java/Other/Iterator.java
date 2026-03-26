package iterator;

interface Iterator {
    //@ requires true;
    //@ ensures result == true || result == false;
    boolean hasNext();
        
        

    //@ requires true;
    //@ ensures result != null;
    Object next();
        
        

}

class SingletonIterator implements Iterator {

    /*@
    predicate objectField(Object o) = true;
    @*/

    Object value;
    boolean done;

    

    
    public SingletonIterator(Object value)
        
        
    {
        this.value = value;
        this.done = false;
        
    }
    
    public boolean hasNext()
        
        
    {
        
        return !done;
        
    }
    
    public Object next()
        
        
    {
        
        done = true;
        return value;
        
    }

}

class IteratorUtil {

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
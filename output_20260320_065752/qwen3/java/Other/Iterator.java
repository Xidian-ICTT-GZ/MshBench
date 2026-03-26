package iterator;

interface Iterator {

    
    
    boolean hasNext();
        
        

    Object next();
        
        

}

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    

    
    public SingletonIterator(Object value)
        
        
    {
        this.value = value;
        this.done = false;
        
    }
    
    //@ requires true;
    //@ ensures true;
    public boolean hasNext()
        
        
    {
        
        return !done;
        
    }
    
    //@ requires true;
    //@ ensures true;
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
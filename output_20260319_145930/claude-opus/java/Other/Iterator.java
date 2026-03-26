package iterator;

/*@
predicate Iterator(Iterator i;);
@*/

interface Iterator {

    //@ requires Iterator(this);
    //@ ensures Iterator(this);
    boolean hasNext();
        
        

    //@ requires Iterator(this);
    //@ ensures Iterator(this);
    Object next();
        
        

}

/*@
predicate SingletonIteratorInv(SingletonIterator i; Object value, boolean done) =
    i.value |-> value &*& i.done |-> done;
@*/

class SingletonIterator implements Iterator {

    Object value;
    boolean done;

    //@ predicate Iterator() = SingletonIteratorInv(this, _, _);

    
    public SingletonIterator(Object value)
        //@ requires true;
        //@ ensures SingletonIteratorInv(this, value, false);
    {
        this.value = value;
        this.done = false;
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
        //@ ensures SingletonIteratorInv(iterator, v, true) &*& result == v;
    {
        Object value = null;
        boolean more = iterator.hasNext();
        while (more)
            //@ invariant SingletonIteratorInv(iterator, v, ?d2) &*& (more ? !d2 : true) &*& (!more ? value == v : true);
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
        SingletonIterator i = new SingletonIterator(o);
        boolean before = i.hasNext();
        //@ assert before == true;

        Object last = IteratorUtil.getLast(i);
        //@ assert last == o;
      
        boolean after = i.hasNext();
        //@ assert after == false;
    }

}
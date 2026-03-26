package iterator.it;

/*@
predicate Iterator(Iterator iter;);
predicate IteratorRemaining(Iterator iter, int remaining);
@*/

public interface Iterator {

    //@ requires Iterator(this);
    //@ ensures Iterator(this);
    boolean hasNext();
        
    //@ requires Iterator(this);
    //@ ensures Iterator(this);
    Object next();

}
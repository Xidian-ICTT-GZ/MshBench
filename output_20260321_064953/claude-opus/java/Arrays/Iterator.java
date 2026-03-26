package iterator.it;

/*@
predicate Iterator(Iterator i;);
@*/

public interface Iterator {

    //@ requires Iterator(this);
    //@ ensures Iterator(this);
    boolean hasNext();
        
    //@ requires Iterator(this);
    //@ ensures Iterator(this);
    Object next();

}
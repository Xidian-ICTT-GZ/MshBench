package iterator.it;

public interface Iterator {

    //@ predicate valid();
    
    //@ requires valid();
    //@ ensures valid();
    boolean hasNext();
    
    //@ requires valid();
    //@ ensures valid();
    Object next();

}
package iterator.it;

public interface Iterator {

    //@ predicate valid() = true;
    
    //@ requires valid();
    //@ ensures true;
    boolean hasNext();
        
    //@ requires valid() &*& hasNext() == true;
    //@ ensures valid();
    Object next();
        
}
package iterator.it;

public interface Iterator {

    //@ predicate valid() = true;
    
    //@ requires valid();
    //@ ensures valid();
    boolean hasNext();
        
    //@ requires valid() &*& hasNext() == true;
    //@ ensures valid();
    Object next();
        
        

}
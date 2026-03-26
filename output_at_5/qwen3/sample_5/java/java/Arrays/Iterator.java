package iterator.it;

public interface Iterator {
    
    //@ requires true;
    //@ ensures result == true || result == false;
    boolean hasNext();
        
    //@ requires true;
    //@ ensures result != null;
    Object next();
        
}
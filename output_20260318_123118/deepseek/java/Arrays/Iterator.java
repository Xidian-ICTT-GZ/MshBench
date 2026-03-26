package iterator.it;

public interface Iterator {

    
    
    boolean hasNext()
    //@ requires true;
    //@ ensures true;
    ;
        
        
        
    Object next()
    //@ requires true;
    //@ ensures true;
    ;
        
        

}
package iterator.it;

public interface Iterator {

    /*@
    predicate iter();
    @*/

    //@ requires iter();
    //@ ensures iter();
    boolean hasNext();

    //@ requires iter();
    //@ ensures iter();
    Object next();

}
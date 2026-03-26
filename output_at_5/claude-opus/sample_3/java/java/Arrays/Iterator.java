package iterator.it;

public interface Iterator {

    /*@
    predicate iter(Iterator this);
    @*/

    //@ requires iter(this);
    //@ ensures iter(this);
    boolean hasNext();

    //@ requires iter(this);
    //@ ensures iter(this);
    Object next();

}
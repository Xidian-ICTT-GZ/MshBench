package iterator.it;

/*@ predicate hasNext_result(Iterator it, boolean b) = true; @*/

public interface Iterator {

    //@ requires true;
    //@ ensures hasNext_result(this, result);
    boolean hasNext();

    //@ requires hasNext_result(this, true);
    //@ ensures true;
    Object next();

}
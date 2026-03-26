package iterator.it;

/*@
predicate iterator(Object iter);
@*/

public interface Iterator {

    //@ requires iterator(this);
    //@ ensures iterator(this);
    boolean hasNext();

    //@ requires iterator(this);
    //@ ensures iterator(this);
    //@ ensures true; // result can be any Object
    Object next();

}
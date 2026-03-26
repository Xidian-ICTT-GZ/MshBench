package iterator.it;

/*@ predicate iterator(Iterator it; list<Object> xs) = 
    true;
@*/

public interface Iterator {

    //@ requires iterator(this, ?xs) &*& xs != nil;
    //@ ensures iterator(this, ?ys) &*& result == true &*& xs == cons(?x, ys);
    boolean hasNext();
    
    //@ requires iterator(this, ?xs) &*& xs != nil;
    //@ ensures iterator(this, ?ys) &*& result == head(xs) &*& xs == cons(result, ys);
    Object next();
    
}
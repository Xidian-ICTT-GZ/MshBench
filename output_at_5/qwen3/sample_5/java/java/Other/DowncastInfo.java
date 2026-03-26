class C {
    int x;

    /*@
    predicate object(C this) = true;
    @*/

    //@ requires true;
    //@ ensures object(this);
    C() {
        
    }

}

class D extends C {
    int y;

    /*@
    predicate object(D this) = object((C)this) &*& true;
    @*/

    //@ requires true;
    //@ ensures object(this);
    D() {
        
    }
    

    /*@
    requires object(this);
    ensures result == this.y &*& object(this);
    */
    int getY() {
        
        return this.y;
        
    }
}

class E extends D {
    int z;
    
    /*@
    predicate object(E this) = object((D)this) &*& true;
    @*/

    //@ requires true;
    //@ ensures object(this);
    E() {
        
    }
    

    /*@
    requires object(this);
    ensures result == super.getY() &*& object(this);
    */
    int getY() {
        
        
        return super.getY();
        
        
    }
}

class Program {
    static int getY(C c)
        
        
    {
        if (c instanceof D) {
            D d = (D)c;
            
            //@ open object(d);
            int res = d.getY();
            //@ close object(d);
            return res;
            
        } else {
            return 0;
        }
    }

    static void test()
        
        
    {
        E e = new E();
        
        getY(e);
    }
}
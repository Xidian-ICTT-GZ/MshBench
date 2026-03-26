class C {
    int x;
    
    /*@
    predicate objectInv(C this) = true;
    @*/
    
    //@ requires true;
    //@ ensures objectInv(this);
    C()
    {
        
    }

    
}

class D extends C {
    int y;

    /*@
    predicate objectInv(D this) = this.objectInv() &*& true;
    @*/

    //@ requires objectInv(this);
    //@ ensures objectInv(this);
    D()
    {
        
    }
    
    //@ requires objectInv(this);
    //@ ensures objectInv(this) &*& result == this.y;
    int getY()
    {
        return this.y;
    }
}

class E extends D {
    int z;
    
    /*@
    predicate objectInv(E this) = this.objectInv() &*& true;
    @*/

    //@ requires objectInv(this);
    //@ ensures objectInv(this);
    E()
    {
        
    }
    
    //@ requires objectInv(this);
    //@ ensures objectInv(this) &*& result == super.getY();
    int getY()
    {
        return super.getY();
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
    static int getY(C c)
    {
        if (c instanceof D) {
            D d = (D)c;
            return d.getY();
        } else {
            return 0;
        }
    }

    //@ requires true;
    //@ ensures true;
    static void test()
    {
        E e = new E();
        getY(e);
    }
}
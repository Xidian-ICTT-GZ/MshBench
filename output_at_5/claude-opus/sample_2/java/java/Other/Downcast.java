class C {
    int x;
    
    /*@
    predicate this_inv() = this.x |-> _;
    @*/
    
    C()
    //@ requires true;
    //@ ensures this_inv();
    {
        //@ close this_inv();
    }

}

class D extends C {
    int y;

    /*@
    predicate this_inv() = this.x |-> _ &*& this.y |-> _;
    @*/

    D()
    //@ requires true;
    //@ ensures this_inv();
    {
        //@ close this_inv();
    }
    
    int getY()
    //@ requires this_inv();
    //@ ensures this_inv() &*& result == this.y;
    {
        //@ open this_inv();
        int tmp = this.y;
        //@ close this_inv();
        return tmp;
    }
}

class E extends D {
    int z;

    /*@
    predicate this_inv() = this.x |-> _ &*& this.y |-> _ &*& this.z |-> _;
    @*/

    E()
    //@ requires true;
    //@ ensures this_inv();
    {
        //@ close this_inv();
    }
    
    int getY()
    //@ requires this_inv();
    //@ ensures this_inv() &*& result == this.y;
    {
        //@ open this_inv();
        int r = this.y; // same as super.getY(), but calls directly to avoid call to super method in VeriFast
        //@ close this_inv();
        return r;
    }
}

class Program {
    static int getY(C c)
    //@ requires true;
    //@ ensures true;
    {
        if (c instanceof D) {
            D d = (D)c;
            //@ open d.this_inv();
            int r = d.getY();
            //@ close d.this_inv();
            return r;
        } else {
            return 0;
        }
    }

    static void test()
    //@ requires true;
    //@ ensures true;
    {
        E e = new E();
        //@ open e.this_inv();
        getY(e);
        //@ close e.this_inv();
    }
}
class C {
    int x;
    
    /*@
    predicate object_inv() = this.x |-> _;
    @*/

    C()
    //@ requires true;
    //@ ensures object_inv();
    {
        //@ close object_inv();
    }
}

class D extends C {
    int y;

    /*@
    // predicate inv for D includes C's inv and y field
    predicate object_inv() = super.object_inv() &*& this.y |-> _;
    @*/

    D()
    //@ requires true;
    //@ ensures object_inv();
    {
        //@ close object_inv();
    }
    
    int getY()
    //@ requires object_inv();
    //@ ensures object_inv() &*& result == this.y;
    {
        //@ open object_inv();
        int tmp = this.y;
        //@ close object_inv();
        return tmp;
    }
}

class E extends D {
    int z;
    
    /*@
    // predicate inv for E includes D's inv and z field
    predicate object_inv() = super.object_inv() &*& this.z |-> _;
    @*/

    E()
    //@ requires true;
    //@ ensures object_inv();
    {
        //@ close object_inv();
    }
    
    int getY()
    //@ requires object_inv();
    //@ ensures object_inv() &*& result == super.getY();
    {
        //@ open object_inv();
        int tmp = super.getY();
        //@ close object_inv();
        return tmp;
    }
}

class Program {
    static int getY(C c)
    //@ requires c != null &*& c instanceof D ? ((D)c).object_inv() : true;
    //@ ensures true;
    {
        if (c instanceof D) {
            D d = (D)c;
            //@ open d.object_inv();
            int result = d.getY();
            //@ close d.object_inv();
            return result;
        } else {
            //@ assume c == null || !(c instanceof D);
            return 0;
        }
    }

    static void test()
    //@ requires true;
    //@ ensures true;
    {
        E e = new E();
        //@ open e.object_inv();
        getY(e);
        //@ close e.object_inv();
    }
}
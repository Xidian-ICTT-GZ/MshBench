class C {
    int x;
    
    /*@
    predicate inv() = this.x |-> _;
    @*/
    
    C()
    //@ requires true;
    //@ ensures inv();
    {
        //@ close inv();
    }

}

class D extends C {
    int y;

    /*@
    predicate inv() = this.x |-> _ &*& this.y |-> _;
    @*/

    D()
    //@ requires true;
    //@ ensures inv();
    {
        //@ close inv();
    }
    
    int getY()
    //@ requires inv();
    //@ ensures inv();
    {
        //@ open inv();
        int tmp = this.y;
        //@ close inv();
        return tmp;
    }
}

class E extends D {
    int z;

    /*@
    predicate inv() = this.x |-> _ &*& this.y |-> _ &*& this.z |-> _;
    @*/

    E()
    //@ requires true;
    //@ ensures inv();
    {
        //@ close inv();
    }
    
    int getY()
    //@ requires inv();
    //@ ensures inv();
    {
        //@ open inv();
        int r = super.getY();
        //@ close inv();
        return r;
    }
}

class Program {
    static int getY(C c)
    //@ requires c != null &*& ((c instanceof D) ? (c instanceof E ? ((E) c).inv() : ((D) c).inv()) : true);
    //@ ensures true;
    {
        if (c instanceof D) {
            if (c instanceof E) {
                E e = (E)c;
                //@ open e.inv();
                int r = e.getY();
                //@ close e.inv();
                return r;
            } else {
                D d = (D)c;
                //@ open d.inv();
                int r = d.getY();
                //@ close d.inv();
                return r;
            }
        } else {
            return 0;
        }
    }

    static void test()
    //@ requires true;
    //@ ensures true;
    {
        E e = new E();
        //@ open e.inv();
        getY(e);
        //@ close e.inv();
    }
}
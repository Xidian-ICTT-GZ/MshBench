/*@ predicate C(C c; int x) = c.x |-> x; @*/
/*@ predicate D(D d; int x, int y) = C(d, x) &*& d.y |-> y; @*/
/*@ predicate E(E e; int x, int y, int z) = D(e, x, y) &*& e.z |-> z; @*/

class C {
    int x;
    
    //@ requires true;
    //@ ensures C(this, 0);
    C()
    {
        
    }
}

class D extends C {
    int y;

    //@ requires true;
    //@ ensures D(this, 0, 0);
    D()
    {
        
    }
    
    //@ requires D(this, ?x, ?y);
    //@ ensures D(this, x, y) &*& result == y;
    int getY()
    {
        return this.y;
    }
}

class E extends D {
    int z;
    
    //@ requires true;
    //@ ensures E(this, 0, 0, 0);
    E()
    {
        
    }
    
    //@ requires E(this, ?x, ?y, ?z);
    //@ ensures E(this, x, y, z) &*& result == y;
    int getY()
    {
        return super.getY();
    }
}

class Program {
    //@ requires C(c, ?x) &*& (c instanceof D ? D((D)c, x, ?y) : true);
    //@ ensures result == (c instanceof D ? ((D)c).y : 0);
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
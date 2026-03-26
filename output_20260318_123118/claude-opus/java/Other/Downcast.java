class C {
    int x;

    /*@ predicate C_inv(C c;) = c.x |-> ?vx; @*/

    C()
        //@ requires true;
        //@ ensures C_inv(this);
    {
        
    }

    
}

class D extends C {
    int y;

    /*@ predicate D_inv(D d;) = C_inv(d) &*& d.y |-> ?vy; @*/
    
    D()
        //@ requires true;
        //@ ensures D_inv(this);
    {
        
    }
    
    int getY()
        //@ requires D_inv(this);
        //@ ensures D_inv(this) &*& result == this.y;
    {
        
        return this.y;
        
    }
}

class E extends D {
    int z;

    /*@ predicate E_inv(E e;) = D_inv(e) &*& e.z |-> ?vz; @*/

    E()
        //@ requires true;
        //@ ensures E_inv(this);
    {
        
    }
    
    int getY()
        //@ requires E_inv(this);
        //@ ensures E_inv(this) &*& result == this.y;
    {
        
        
        return super.getY();
        
        
    }
}

class Program {
    static int getY(C c)
        //@ requires c != null &*& ( (c instanceof D ==> D_inv((D)c)) || !(c instanceof D) );
        //@ ensures (c instanceof D ==> D_inv((D)c) &*& result == ((D)c).y) &*& (! (c instanceof D) ==> result == 0);
    {
        if (c instanceof D) {
            D d = (D)c;
            
            return d.getY();
            
        } else {
            return 0;
        }
    }

    static void test()
        //@ requires true;
        //@ ensures true;
    {
        E e = new E();
        //@ open E_inv(e);
        getY(e);
        //@ close E_inv(e);
    }
}
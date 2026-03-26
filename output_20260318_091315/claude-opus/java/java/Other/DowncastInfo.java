class C {
    int x;
    
    /*@ predicate C_inv(C c) = c->x |-> _; @*/

    //@ requires true;
    //@ ensures C_inv(this);
    C()
    {
        
    }

    
}

class D extends C {
    int y;

    /*@ predicate D_inv(D d) = C_inv(d) &*& d->y |-> _; @*/

    //@ requires true;
    //@ ensures D_inv(this);
    D()
    {
        
    }
    
    //@ requires D_inv(this);
    //@ ensures D_inv(this) &*& result == this.y;
    int getY()
    {
        
        return this.y;
        
    }
}

class E extends D {
    int z;
    
    /*@ predicate E_inv(E e) = D_inv(e) &*& e->z |-> _; @*/

    //@ requires true;
    //@ ensures E_inv(this);
    E()
    {
        
    }
    
    //@ requires E_inv(this);
    //@ ensures E_inv(this) &*& result == this.y;
    int getY()
    {
        
        
        return super.getY();
        
        
    }
}

class Program {
    //@ predicate C_dyn_inv(C c) = 
    //@     (c instanceof E ==> E_inv((E)c)) ||
    //@     (c instanceof D && !(c instanceof E) ==> D_inv((D)c)) ||
    //@     (!(c instanceof D) ==> C_inv(c));
    
    //@ requires C_dyn_inv(c);
    //@ ensures C_dyn_inv(c) &*& result == (c instanceof D ? ((D)c).y : 0);
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
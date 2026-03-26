class C {
    int x;
    
    //@ predicate C_inv(C this) = this->x |-> _;
    
    C()
        //@ requires true;
        //@ ensures C_inv(this);
    {
        
    }

    
}

class D extends C {
    int y;

    //@ predicate D_inv(D this) = C_inv(this) &*& this->y |-> _;
    
    D()
        //@ requires true;
        //@ ensures D_inv(this);
    {
        
    }
        
    //@ requires D_inv(this);
    //@ ensures D_inv(this) &*& result == this->y;
    int getY()
    {
        return this.y;
    }
}

class E extends D {
    int z;
    
    //@ predicate E_inv(E this) = D_inv(this) &*& this->z |-> _;
    
    E()
        //@ requires true;
        //@ ensures E_inv(this);
    {
        
    }
    
    //@ requires E_inv(this);
    //@ ensures E_inv(this) &*& result == this->y;
    int getY()
    {
        return super.getY();
    }
}

class Program {
    //@ predicate C_or_D_inv(C c) =
    //@     (c instanceof D ==> D_inv((D)c)) &*&
    //@     (c instanceof E ==> E_inv((E)c)) &*&
    //@     (!(c instanceof D) ==> C_inv(c));
    
    //@ requires C_or_D_inv(c);
    //@ ensures C_or_D_inv(c) &*& (c instanceof D ==> result == ((D)c).y) &*& (!(c instanceof D) ==> result == 0);
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
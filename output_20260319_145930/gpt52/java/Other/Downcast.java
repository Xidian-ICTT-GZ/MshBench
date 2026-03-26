/*@

predicate C_inv(C c) = c.x |-> _;

predicate D_inv(D d) = C_inv(d) &*& d.y |-> _;

predicate E_inv(E e) = D_inv(e) &*& e.z |-> _;

@*/
class C {
    int x;
    
    C()
        //@ requires true;
        //@ ensures C_inv(this);
    {
        //@ close C_inv(this);
    }

    
}

class D extends C {
    int y;

    D()
        //@ requires true;
        //@ ensures D_inv(this);
    {
        //@ close C_inv(this);
        //@ close D_inv(this);
    }
    
    

    
    int getY()
        //@ requires D_inv(this);
        //@ ensures D_inv(this) &*& result == this.y;
    {
        //@ open D_inv(this);
        int res = this.y;
        //@ close D_inv(this);
        return res;
        
    }
}

class E extends D {
    int z;
    
    E()
        //@ requires true;
        //@ ensures E_inv(this);
    {
        //@ close C_inv(this);
        //@ close D_inv(this);
        //@ close E_inv(this);
    }
    
    

    
    int getY()
        //@ requires E_inv(this);
        //@ ensures E_inv(this) &*& result == this.y;
    {
        //@ open E_inv(this);
        //@ open D_inv(this);
        //@ open C_inv(this);
        int res = super.getY();
        //@ close C_inv(this);
        //@ close D_inv(this);
        //@ close E_inv(this);
        return res;
        
        
    }
}

class Program {
    static int getY(C c)
        //@ requires c instanceof D ? D_inv((D)c) : C_inv(c);
        //@ ensures c instanceof D ? D_inv((D)c) : C_inv(c);
    {
        if (c instanceof D) {
            //@ assert c instanceof D;
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
        //@ assert E_inv(e);
        
        getY(e);
    }
}
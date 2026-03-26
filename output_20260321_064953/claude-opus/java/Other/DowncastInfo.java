class C {
    int x;
    
    /*@
      predicate c_inv(C this) = this|->x; 
    @*/
    
    C()
        //@ requires true;
        //@ ensures c_inv(this);
    {
        //@ close c_inv(this);
    }

    
}

class D extends C {
    int y;

    /*@
      predicate d_inv(D this) = c_inv(this) &*& this|->y;
    @*/
    
    D()
        //@ requires true;
        //@ ensures d_inv(this);
    {
        //@ close d_inv(this);
    }
    
    

    
    int getY()
        //@ requires d_inv(this);
        //@ ensures d_inv(this) &*& result == this.y;
    {
        //@ open d_inv(this);
        int r = this.y;
        //@ close d_inv(this);
        return r;
    }
}

class E extends D {
    int z;
    
    /*@
      predicate e_inv(E this) = d_inv(this) &*& this|->z;
    @*/
    
    E()
        //@ requires true;
        //@ ensures e_inv(this);
    {
        //@ close e_inv(this);
    }
    
    

    
    int getY()
        //@ requires e_inv(this);
        //@ ensures e_inv(this) &*& result == super.getY();
    {
        //@ open e_inv(this);
        int r = super.getY();
        //@ close e_inv(this);
        return r;
    }
}

class Program {
    static int getY(C c)
        //@ requires c != null &*& (c instanceof D ? true : true);
        //@ ensures true;
    {
        if (c instanceof D) {
            D d = (D)c;
            //@ open d_inv(d);
            int r = d.getY();
            //@ close d_inv(d);
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
        getY(e);
    }
}
class C {
    int x;
    /*@
      predicate thisClassValid() = this.x |-> _;
     @*/
    
    C()
        //@ requires true;
        //@ ensures thisClassValid();
    {
        //@ close thisClassValid();
    }

    
}

class D extends C {
    int y;
    /*@
      predicate thisClassValid() = this.x |-> _ &*& this.y |-> _;
     @*/

    D()
        //@ requires true;
        //@ ensures thisClassValid();
    {
        //@ close thisClassValid();
    }
    
    

    
    int getY()
        //@ requires thisClassValid();
        //@ ensures thisClassValid() &*& result == this.y;
    {
        //@ open thisClassValid();
        
        int tmp = this.y;
        
        //@ close thisClassValid();
        return tmp;
    }
}

class E extends D {
    int z;
    /*@
      predicate thisClassValid() = this.x |-> _ &*& this.y |-> _ &*& this.z |-> _;
     @*/
    
    E()
        //@ requires true;
        //@ ensures thisClassValid();
    {
        //@ close thisClassValid();
    }
    
    

    
    int getY()
        //@ requires thisClassValid();
        //@ ensures thisClassValid() &*& result == super.getY();
    {
        //@ open thisClassValid();
        int tmp = super.getY();
        //@ close thisClassValid();
        return tmp;
    }
}

class Program {
    static int getY(C c)
        //@ requires true;
        //@ ensures true;
    {
        if (c instanceof D) {
            D d = (D)c;
            //@ open d.thisClassValid();
            int tmp = d.getY();
            //@ close d.thisClassValid();
            return tmp;
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
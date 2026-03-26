class C {
    int x;
    
    /*@ predicate this_class_C(C o) = o == this; @*/
    
    C()
        //@ requires true;
        //@ ensures this_class_C(this);
    {
        
    }

    
}

class D extends C {
    int y;

    /*@ predicate this_class_D(D o) = this_class_C(o) &*& o == this; @*/

    D()
        //@ requires this_class_C(this);
        //@ ensures this_class_D(this);
    {
        
    }
    
    

    
    int getY()
        //@ requires this_class_D(this);
        //@ ensures this_class_D(this) &*& result == this.y;
    {
        
        return this.y;
        
    }
}

class E extends D {
    int z;
    
    /*@ predicate this_class_E(E o) = this_class_D(o) &*& o == this; @*/

    E()
        //@ requires this_class_D(this);
        //@ ensures this_class_E(this);
    {
        
    }
    
    

    
    int getY()
        //@ requires this_class_E(this);
        //@ ensures this_class_E(this) &*& result == super.getY();
    {
        
        
        return super.getY();
        
        
    }
}

class Program {
    static int getY(C c)
        //@ requires true;
        //@ ensures true;
    {
        if (c instanceof D) {
            D d = (D)c;
            //@ open this_class_D(d);
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
        
        getY(e);
    }
}
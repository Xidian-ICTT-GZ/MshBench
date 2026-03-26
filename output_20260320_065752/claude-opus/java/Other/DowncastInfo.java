class C {
    int x;
    
    //@ requires true;
    //@ ensures true;
    C()
    {
        
    }

    
}

class D extends C {
    int y;

    //@ requires true;
    //@ ensures true;
    D()
    {
        
    }
    
    //@ requires this.D(this.y);
    //@ ensures this.D(this.y);
    //@ predicate D(int y) = this.y |-> y;
    
    //@ requires this.D(?vy);
    //@ ensures this.D(vy) &*& result == vy;
    int getY()
    {
        //@ open this.D(?vy);
        return this.y;
        //@ close this.D(vy);
    }
}

class E extends D {
    int z;
    
    //@ requires true;
    //@ ensures true;
    E()
    {
        
    }
    
    //@ requires this.D(?vy);
    //@ ensures this.D(vy) &*& result == vy;
    int getY()
    {
        return super.getY();
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
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
class C {
    int x;
    
    C()
        //@ requires true;
        //@ ensures this.x |-> 0;
    {
        
    }

    
}

class D extends C {
    int y;

    D()
        //@ requires true;
        //@ ensures this.x |-> 0 &*& this.y |-> 0;
    {
        
    }
    
    int getY()
        //@ requires this.y |-> ?v;
        //@ ensures this.y |-> v &*& result == v;
    {
        
        return this.y;
        
    }
}

class E extends D {
    int z;
    
    E()
        //@ requires true;
        //@ ensures this.x |-> 0 &*& this.y |-> 0 &*& this.z |-> 0;
    {
        
    }
    
    int getY()
        //@ requires this.y |-> ?v;
        //@ ensures this.y |-> v &*& result == v;
    {
        
        
        return super.getY();
        
        
    }
}

class Program {
    static int getY(C c)
        //@ requires c != null &*& c.x |-> ?vx &*& (c instanceof D ? ((D)c).y |-> ?vy : true) &*& (c instanceof E ? ((E)c).z |-> ?vz : true);
        //@ ensures c.x |-> vx &*& (c instanceof D ? ((D)c).y |-> vy : true) &*& (c instanceof E ? ((E)c).z |-> vz : true);
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
        
        getY(e);
    }
}
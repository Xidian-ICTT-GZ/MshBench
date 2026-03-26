class C {
    int x;
    
    C()
        
        
    {
        
    }

    
}

class D extends C {
    int y;

    D()
        
        
    {
        
    }
    
    



















    
    int getY()
        
        
    {
        
        return this.y;
        
    }
}

class E extends D {
    int z;
    
    E()
        
        
    {
        
    }
    
    






















    
    int getY()
        
        
    {
        
        
        return super.getY();
        
        
    }
}

class Program {
    static int getY(C c)
        
        
    {
        if (c instanceof D) {
            D d = (D)c;
            
            return d.getY();
            
        } else {
            return 0;
        }
    }

    static void test()
        
        
    {
        E e = new E();
        
        getY(e);
    }
}
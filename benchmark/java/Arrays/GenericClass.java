import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;



public class GenericClass<T>{
	public T field;
	public GenericClass(T f)
	
	
	{
		field = f;
	}
	
	public T add(T arg)
	
	
	{
		field = arg;
		return field;
	}
	
	public T get()
	
	
	{
		return field;
	}
}

public class Foo<T> {
	public Foo(T arg)
	
	
	{
		GenericClass<T> b = new GenericClass<T>(arg);
	}
}






public interface Parent<A,B>{
	public A get1(A arg1);
	public B get2();
}

public interface Child<C,D> extends Parent<D,C>{
	public D get1(D arg1);
	public C get2();
}

public class ChildClass<C,D> implements Parent<D,C>{
	public D get1(D arg1) {return null;}
	public C get2() {return null;}
}


public abstract class AbstractParentClass<A,B> {
	public abstract A get1(A arg1);
}
public class ChildClassInheritance<C,D> extends AbstractParentClass<C,D>{
	public C get1(C arg1){return null;}
}

public class HelloWorld 
{
  public static GenericClass<GenericClass<Foo> > genericInstance;
  
  public static void main(String[] args) 
    
    
  {
    String[] sentence = {"Hello", "World"};
    List<String> sentenceList = Arrays.<String>asList(sentence);
    Foo<String> foo = new Foo<String>("test");
    GenericClass<String> simple = new GenericClass<String>("Example");
    GenericClass<GenericClass<String> > nested = new GenericClass<GenericClass<String> >(new GenericClass<String>("foo"));
    nested.add(new GenericClass<String>("hello"));
    GenericClass<String> s = nested.get();   
    
    List<String> l = new ArrayList< >();
    l.add("foo");
    String abba = l.get(0);
  }
}

import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;

public class GenericClass<T>{
	public T field;
	//@ predicate inv() = this.field |-> ?f;
	public GenericClass(T f)
	//@ requires true;
	//@ ensures inv();
	
	
	{
		//@ close inv();
		field = f;
		//@ close inv();
	}
	
	public T add(T arg)
	//@ requires inv();
	//@ ensures inv() &*& result == arg;
	
	
	{
		//@ open inv();
		field = arg;
		//@ close inv();
		return field;
	}
	
	public T get()
	//@ requires inv();
	//@ ensures inv() &*& result == field;
	
	
	{
		//@ open inv();
		T res = field;
		//@ close inv();
		return res;
	}
}

public class Foo<T> {
	public Foo(T arg)
	//@ requires true;
	//@ ensures true;
	
	
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
	public D get1(D arg1) 
	//@ requires true;
	//@ ensures result == null;
	{return null;}
	public C get2() 
	//@ requires true;
	//@ ensures result == null;
	{return null;}
}

public abstract class AbstractParentClass<A,B> {
	public abstract A get1(A arg1);
}
public class ChildClassInheritance<C,D> extends AbstractParentClass<C,D>{
	public C get1(C arg1)
	//@ requires true;
	//@ ensures result == null;
	{return null;}
}

public class HelloWorld 
{
  public static GenericClass<GenericClass<Foo> > genericInstance;
  
  public static void main(String[] args) 
  //@ requires true;
  //@ ensures true;
    
    
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
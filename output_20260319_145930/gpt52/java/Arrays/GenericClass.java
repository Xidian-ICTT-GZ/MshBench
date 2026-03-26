import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;

/*@

predicate genericClass<T>(GenericClass<T> o; T f) =
    o != null &*& o.field |-> f;

@*/

public class GenericClass<T>{
	public T field;
	//@ requires true;
	//@ ensures genericClass<T>(this, f);
	public GenericClass(T f)
	
	
	{
		//@ close genericClass<T>(this, null);
		field = f;
		//@ open genericClass<T>(this, null);
		//@ close genericClass<T>(this, f);
	}
	
	//@ requires genericClass<T>(this, ?old);
	//@ ensures genericClass<T>(this, arg) &*& result == arg;
	public T add(T arg)
	
	
	{
		//@ open genericClass<T>(this, old);
		field = arg;
		//@ close genericClass<T>(this, arg);
		return field;
	}
	
	//@ requires genericClass<T>(this, ?f);
	//@ ensures genericClass<T>(this, f) &*& result == f;
	public T get()
	
	
	{
		//@ open genericClass<T>(this, f);
		T res = field;
		//@ close genericClass<T>(this, f);
		return res;
	}
}

public class Foo<T> {
	//@ requires true;
	//@ ensures true;
	public Foo(T arg)
	
	
	{
		GenericClass<T> b = new GenericClass<T>(arg);
		//@ open genericClass<T>(b, arg);
		//@ close genericClass<T>(b, arg);
	}
}

public interface Parent<A,B>{
	//@ requires true;
	//@ ensures true;
	public A get1(A arg1);
	//@ requires true;
	//@ ensures true;
	public B get2();
}

public interface Child<C,D> extends Parent<D,C>{
	//@ requires true;
	//@ ensures true;
	public D get1(D arg1);
	//@ requires true;
	//@ ensures true;
	public C get2();
}

public class ChildClass<C,D> implements Parent<D,C>{
	//@ requires true;
	//@ ensures result == null;
	public D get1(D arg1) {return null;}
	//@ requires true;
	//@ ensures result == null;
	public C get2() {return null;}
}

public abstract class AbstractParentClass<A,B> {
	//@ requires true;
	//@ ensures true;
	public abstract A get1(A arg1);
}
public class ChildClassInheritance<C,D> extends AbstractParentClass<C,D>{
	//@ requires true;
	//@ ensures result == null;
	public C get1(C arg1){return null;}
}

public class HelloWorld 
{
  public static GenericClass<GenericClass<Foo> > genericInstance;
  
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args) 
    
    
  {
    String[] sentence = {"Hello", "World"};
    List<String> sentenceList = Arrays.<String>asList(sentence);
    Foo<String> foo = new Foo<String>("test");
    GenericClass<String> simple = new GenericClass<String>("Example");
    GenericClass<GenericClass<String> > nested = new GenericClass<GenericClass<String> >(new GenericClass<String>("foo"));
    //@ open genericClass<GenericClass<String> >(nested, ?inner0);
    //@ close genericClass<GenericClass<String> >(nested, inner0);
    nested.add(new GenericClass<String>("hello"));
    GenericClass<String> s = nested.get();   
    
    List<String> l = new ArrayList< >();
    l.add("foo");
    String abba = l.get(0);
  }
}
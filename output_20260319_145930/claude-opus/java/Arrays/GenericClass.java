import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;

/*@
predicate GenericClass_pred<T>(GenericClass<T> gc;) =
    gc.field |-> _;
@*/

public class GenericClass<T>{
	public T field;
	public GenericClass(T f)
	//@ requires true;
	//@ ensures GenericClass_pred<T>(this);
	{
		field = f;
		//@ close GenericClass_pred<T>(this);
	}
	
	public T add(T arg)
	//@ requires GenericClass_pred<T>(this);
	//@ ensures GenericClass_pred<T>(this);
	{
		//@ open GenericClass_pred<T>(this);
		field = arg;
		//@ close GenericClass_pred<T>(this);
		return field;
	}
	
	public T get()
	//@ requires GenericClass_pred<T>(this);
	//@ ensures GenericClass_pred<T>(this);
	{
		//@ open GenericClass_pred<T>(this);
		T tmp = field;
		//@ close GenericClass_pred<T>(this);
		return tmp;
	}
}

public class Foo<T> {
	public Foo(T arg)
	//@ requires true;
	//@ ensures true;
	{
		GenericClass<T> b = new GenericClass<T>(arg);
		//@ open GenericClass_pred<T>(b);
	}
}

public interface Parent<A,B>{
	public A get1(A arg1);
	//@ requires true;
	//@ ensures true;
	public B get2();
	//@ requires true;
	//@ ensures true;
}

public interface Child<C,D> extends Parent<D,C>{
	public D get1(D arg1);
	//@ requires true;
	//@ ensures true;
	public C get2();
	//@ requires true;
	//@ ensures true;
}

public class ChildClass<C,D> implements Parent<D,C>{
	public D get1(D arg1)
	//@ requires true;
	//@ ensures true;
	{return null;}
	public C get2()
	//@ requires true;
	//@ ensures true;
	{return null;}
}

public abstract class AbstractParentClass<A,B> {
	public abstract A get1(A arg1);
	//@ requires true;
	//@ ensures true;
}
public class ChildClassInheritance<C,D> extends AbstractParentClass<C,D>{
	public C get1(C arg1)
	//@ requires true;
	//@ ensures true;
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
    //@ open GenericClass_pred<String>(simple);
    //@ open GenericClass_pred<GenericClass<String> >(nested);
    //@ close GenericClass_pred<GenericClass<String> >(nested);
    nested.add(new GenericClass<String>("hello"));
    GenericClass<String> s = nested.get();   
    //@ open GenericClass_pred<GenericClass<String> >(nested);
    
    List<String> l = new ArrayList< >();
    l.add("foo");
    String abba = l.get(0);
  }
}
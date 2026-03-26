package chat;

import java.io.*;
import java.net.*;
import java.util.*;

class Member {
    String nick;
    Writer writer;
    
    /*@ predicate member_object(Member m;) = 
          m.nick |-> ?nick &*&
          m.writer |-> ?writer;
    @*/
    
    //@ requires nick != null &*& writer != null;
    //@ ensures member_object(this);
    public Member(String nick, Writer writer)
        
    {
        this.nick = nick;
        this.writer = writer;
        
    }
}
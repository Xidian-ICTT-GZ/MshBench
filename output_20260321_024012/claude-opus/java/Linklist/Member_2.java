package chat;

import java.io.*;
import java.net.*;
import java.util.*;

/*@
predicate member_inv(Member m) = m.nick |-> ?nick &*& m.writer |-> ?writer;
@*/

class Member {
    String nick;
    Writer writer;
    
    //@ requires true;
    //@ ensures member_inv(this);
    public Member(String nick, Writer writer)
        
        
    {
        this.nick = nick;
        this.writer = writer;
        
    }
}
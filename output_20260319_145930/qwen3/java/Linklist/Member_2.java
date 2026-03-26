package chat;

import java.io.*;
import java.net.*;
import java.util.*;

/*@ predicate member(Member m; String nick, Writer w) = 
    m.nick |-> nick &*& m.writer |-> w;
@*/

class Member {
    String nick;
    Writer writer;
    
    //@ requires true;
    //@ ensures member(this, nick, writer);
    public Member(String nick, Writer writer)
    {
        this.nick = nick;
        this.writer = writer;
        //@ close member(this, nick, writer);
    }
}
package chat;

import java.io.*;
import java.net.*;
import java.util.*;

/*@

predicate member(Member m; String nick, Writer writer) =
    m != null &*&
    m.nick |-> nick &*&
    m.writer |-> writer;

@*/

class Member {
    String nick;
    Writer writer;
    
    public Member(String nick, Writer writer)
    //@ requires true;
    //@ ensures member(this, nick, writer);
    {
        this.nick = nick;
        this.writer = writer;
        
    }
}
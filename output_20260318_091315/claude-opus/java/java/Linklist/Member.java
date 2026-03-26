package chat;

import java.io.*;
import java.net.*;
import java.util.*;

class Member {
    String nick;
    Writer writer;
    
    /*@ predicate member(Member m; String nick, Writer writer) =
          m.nick |-> nick &*& m.writer |-> writer;
    @*/
    
    //@ requires nick != null &*& writer != null;
    //@ ensures member(this, nick, writer);
    public Member(String nick, Writer writer)
    {
        this.nick = nick;
        this.writer = writer;
    }
}
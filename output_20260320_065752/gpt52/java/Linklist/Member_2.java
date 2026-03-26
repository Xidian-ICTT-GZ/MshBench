package chat;

import java.io.*;
import java.net.*;
import java.util.*;

class Member {
    String nick;
    Writer writer;
    
    /*@
    predicate member(String n, Writer w) =
        this.nick |-> n &*& this.writer |-> w;
    @*/
    
    public Member(String nick, Writer writer)
        //@ requires true;
        //@ ensures this.member(nick, writer);
        
    {
        //@ close this.member(_, _);
        this.nick = nick;
        //@ open this.member(_, _);
        this.writer = writer;
        //@ close this.member(nick, writer);
        
    }
}
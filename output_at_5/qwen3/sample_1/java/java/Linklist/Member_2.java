package chat;

import java.io.*;
import java.net.*;
import java.util.*;

class Member {
    String nick;
    Writer writer;
    
    public Member(String nick, Writer writer)
        //@ requires true;
        //@ ensures this.nick == nick &*& this.writer == writer;
    {
        this.nick = nick;
        this.writer = writer;
        
    }
}
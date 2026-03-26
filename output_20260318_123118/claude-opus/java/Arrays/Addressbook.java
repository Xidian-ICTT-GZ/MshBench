package Addressbook;

import javacard.framework.*;

public final class Addressbook extends Applet {

    private static final byte Store_CLA = (byte) 0xB0;

    private static final byte ADD = (byte) 0x10;
    private static final byte DELETE = (byte) 0x20;
    private static final byte SEARCH = (byte) 0x30;
    private static final byte ADDGROUP = (byte) 0x40;
    private static final byte DELETEGROUP = (byte) 0x50;
    private static final byte ADDCONTACTTOGROUP = (byte) 0x41;
    private static final byte REMOVECONTACTFROMGROUP = (byte) 0x42;
    private static final byte SEARCHINGROUP = (byte) 0x43;
    private static final byte FILTERCONTACTS = (byte) 0x61;

    private static final byte SW_ADDRESSBOOK_FULL = (byte) 0x5300;
    private static final byte SW_PERSON_NOT_FOUND = (byte) 0x2100;
    private static final byte SW_GROUP_NOT_FOUND = (byte) 0x6100;
    private static final byte SW_GROUPBOOK_FULL = (byte) 0x6200;
    private static final byte SW_GROUP_FULL = (byte) 0x6300;
    private static final byte SW_NO_PERSON_FOUND = (byte) 0x4000;

    private static final short NR_LENGTH = 5;
    private static final short NAME_LENGTH = 15;
    private static final short RECORD_LENGTH = 20;
    private static final short GROUPNAME_LENGTH = 10;
    private static final short GROUPNUMBERS_LENGTH = 10;

    private static byte[] zeros;
    private static byte[] phoneNbs;
    private static short[] emptyPhoneNbs;
    private static byte[] groupnames;
    private static byte[] groupnbs;
    private static short[] emptyGroups;
    private static byte[] filteredNames;

    /*@ 
      predicate phoneNb_slot(int i, byte[] phoneNbs, short[] emptyPhoneNbs) =
        0 <= i &*& i < emptyPhoneNbs.length &*&
        emptyPhoneNbs[i] == 0 || emptyPhoneNbs[i] == 1 &*&
        phoneNbs != null &*& phoneNbs.length >= (i+1)*RECORD_LENGTH;

      predicate phoneNbs_invariant(short[] emptyPhoneNbs, byte[] phoneNbs) =
        emptyPhoneNbs != null &*& phoneNbs != null &*&
        emptyPhoneNbs.length * RECORD_LENGTH <= phoneNbs.length &*&
        length(emptyPhoneNbs) == 20 &*& length(phoneNbs) == 400 &*&
        forall(i: int) (0 <= i && i < length(emptyPhoneNbs) ==> 
            phoneNbs_slot(i, phoneNbs, emptyPhoneNbs));

      predicate group_slot(int i, byte[] groupnames, short[] emptyGroups, byte[] groupnbs) =
        0 <= i &*& i < length(emptyGroups) &*&
        (emptyGroups[i] == 0 || emptyGroups[i] == 1) &*&
        groupnames != null &*& groupnames.length >= (i+1)*GROUPNAME_LENGTH &*&
        groupnbs != null &*& groupnbs.length >= (i+1)*GROUPNUMBERS_LENGTH;

      predicate groups_invariant(short[] emptyGroups, byte[] groupnames, byte[] groupnbs) =
        emptyGroups != null &*& groupnames != null &*& groupnbs != null &*&
        length(emptyGroups) == 10 &*&
        length(groupnames) == 100 &*&
        length(groupnbs) == 100 &*&
        forall(i: int) (0 <= i && i < length(emptyGroups) ==>
            group_slot(i, groupnames, emptyGroups, groupnbs));
    @*/

    public static void install(byte[] bArray, short bOffset, byte bLength)
        //@ requires true;
        //@ ensures true;
    {
        Addressbook addressbook = new Addressbook();
        addressbook.register();
    }

    protected Addressbook()
        //@ requires true;
        //@ ensures phoneNbs_invariant(emptyPhoneNbs, phoneNbs) &*& groups_invariant(emptyGroups, groupnames, groupnbs) &*& filteredNames != null &*& length(filteredNames) == 400 &*& zeros != null &*& length(zeros) == 20;
    {
        phoneNbs = new byte[400];
        emptyPhoneNbs = new short[20];
        zeros = new byte[20];
        groupnames = new byte[100];
        groupnbs = new byte[100];
        emptyGroups = new short[10];
        filteredNames = new byte[400];

        for(short i = 0; i < 100; i++)
            //@ invariant 0 <= i &*& i <= 100 &*& groupnbs != null &*& length(groupnbs) == 100;
        {
            groupnbs[i] = (byte)0;
        }
    }

    public void process(APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() |-> ?abuffer &*& length(abuffer) >= 5;
        //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        if(selectingApplet())
            return;

        if(abuffer[ISO7816.OFFSET_CLA] != Store_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);

        switch(abuffer[ISO7816.OFFSET_INS]){
            case ADD: add(apdu); return;
            case DELETE: delete(apdu); return;
            case SEARCH: search(apdu); return;
            case ADDGROUP: addGroup(apdu); return;
            case DELETEGROUP: deleteGroup(apdu); return;
            case ADDCONTACTTOGROUP: addContactToGroup(apdu); return;
            case REMOVECONTACTFROMGROUP: removeContactFromGroup(apdu); return;
            case SEARCHINGROUP: searchInGroup(apdu); return;
            case FILTERCONTACTS: filterContacts(apdu); return;
            default: ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }

    private void add(APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() |-> ?abuffer &*& length(abuffer) >= ISO7816.OFFSET_LC + RECORD_LENGTH &*& array_slice(abuffer, ISO7816.OFFSET_LC, 1, _) == [RECORD_LENGTH];
        //@ requires phoneNbs != null &*& emptyPhoneNbs != null &*& length(phoneNbs) == 400 &*& length(emptyPhoneNbs) == 20;
        //@ ensures phoneNbs_invariant(emptyPhoneNbs, phoneNbs);
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != RECORD_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyPhoneNbs.length;

        boolean added = false;

        //@ int i = 0;
        for(short i=0;i<length;i++)
            //@ invariant 0 <= i &*& i <= length &*& phoneNbs_invariant(emptyPhoneNbs, phoneNbs);
        {
            short item = emptyPhoneNbs[i];

            if(item == 0 && added==false){
                JCSystem.beginTransaction();
                added = true;

                emptyPhoneNbs[i] = 1;
                Util.arrayCopy(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), (short) RECORD_LENGTH);
                JCSystem.commitTransaction();
            }
        }

        if(!added)
            ISOException.throwIt(SW_ADDRESSBOOK_FULL);
    }

    private void delete(APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() |-> ?abuffer &*& length(abuffer) >= ISO7816.OFFSET_LC + NAME_LENGTH &*& array_slice(abuffer, ISO7816.OFFSET_LC, 1, _) == [NAME_LENGTH];
        //@ requires phoneNbs != null &*& emptyPhoneNbs != null &*& length(phoneNbs) == 400 &*& length(emptyPhoneNbs) == 20;
        //@ ensures phoneNbs_invariant(emptyPhoneNbs, phoneNbs);
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyPhoneNbs.length;

        for(short i=0;i<length;i++)
            //@ invariant 0 <= i &*& i <= length &*& phoneNbs_invariant(emptyPhoneNbs, phoneNbs);
        {
            short item = emptyPhoneNbs[i];

            if(item == 1){
                short equal = (short)Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH);

                if(equal == 0){
                    JCSystem.beginTransaction();

                    emptyPhoneNbs[i] = 0;

                    Util.arrayCopy(zeros,(short)0,phoneNbs,(short)(i * RECORD_LENGTH),(short) RECORD_LENGTH);

                    JCSystem.commitTransaction();
                }
            }
        }
    }

    private void search(APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() |-> ?abuffer &*& length(abuffer) >= ISO7816.OFFSET_LC + NAME_LENGTH &*& array_slice(abuffer, ISO7816.OFFSET_LC, 1, _) == [NAME_LENGTH];
        //@ requires phoneNbs != null &*& emptyPhoneNbs != null &*& length(phoneNbs) == 400 &*& length(emptyPhoneNbs) == 20;
        //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyPhoneNbs.length;

        boolean found = false;

        for(short i=0;i<length;i++)
            //@ invariant 0 <= i &*& i <= length;
        {
            short item = emptyPhoneNbs[i];

            if(item == 1 && found == false){
                if(Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH) == 0){
                    found = true;
                    apdu.setOutgoing();
                    apdu.setOutgoingLength(NR_LENGTH);
                    apdu.sendBytesLong(phoneNbs, (short)((i * RECORD_LENGTH)+NAME_LENGTH), NR_LENGTH);
                }
            }
        }

        if(found == false){
            ISOException.throwIt(SW_PERSON_NOT_FOUND);
        }
    }

    private void addGroup (APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() |-> ?abuffer &*& length(abuffer) >= ISO7816.OFFSET_LC + GROUPNAME_LENGTH &*& array_slice(abuffer, ISO7816.OFFSET_LC, 1, _) == [GROUPNAME_LENGTH];
        //@ requires groupnames != null &*& emptyGroups != null &*& groupnbs != null &*& length(groupnames) == 100 &*& length(emptyGroups) == 10 &*& length(groupnbs) == 100;
        //@ ensures groups_invariant(emptyGroups, groupnames, groupnbs);
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != GROUPNAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyGroups.length;

        boolean added = false;

        for(short i=0;i<length;i++)
            //@ invariant 0 <= i &*& i <= length &*& groups_invariant(emptyGroups, groupnames, groupnbs);
        {
            short item = emptyGroups[i];

            if(item == 0 && added==false){
                JCSystem.beginTransaction();
                added = true;

                emptyGroups[i] = 1;

                Util.arrayCopy(abuffer,(short)ISO7816.OFFSET_CDATA,groupnames,(short)(i * GROUPNAME_LENGTH),(short) GROUPNAME_LENGTH);

                JCSystem.commitTransaction();
            }
        }

        if(added == false){
            ISOException.throwIt(SW_GROUPBOOK_FULL);
        }
    }

    private void addContactToGroup (APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() |-> ?abuffer &*& length(abuffer) >= ISO7816.OFFSET_LC + (NAME_LENGTH + GROUPNAME_LENGTH) &*& array_slice(abuffer, ISO7816.OFFSET_LC, 1, _) == [NAME_LENGTH + GROUPNAME_LENGTH];
        //@ requires phoneNbs != null &*& emptyPhoneNbs != null &*& length(phoneNbs) == 400 &*& length(emptyPhoneNbs) == 20 &*& groupnames != null &*& emptyGroups != null &*& groupnbs != null &*& length(groupnames) == 100 &*& length(emptyGroups) == 10 &*& length(groupnbs) == 100;
        //@ ensures groups_invariant(emptyGroups, groupnames, groupnbs) &*& phoneNbs_invariant(emptyPhoneNbs, phoneNbs);
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != (NAME_LENGTH + GROUPNAME_LENGTH))
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyPhoneNbs.length;

        boolean found = false;
        byte contactnb = 0;

        for(short i=0;i<length;i++)
            //@ invariant 0 <= i &*& i <= length;
        {
            short equal = Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH);

            if(found==false && equal == 0 ){
                found = true;

                contactnb = (byte)(short)(i+1);
            }
        }

        if(found == false)
            ISOException.throwIt(SW_PERSON_NOT_FOUND);

        short g_length = (short) emptyGroups.length;

        boolean g_found = false;
        boolean added = false;

        for(short i=0;i<g_length;i++)
            //@ invariant 0 <= i &*& i <= g_length;
        {
            short equal = Util.arrayCompare(abuffer, (short)(ISO7816.OFFSET_CDATA + NAME_LENGTH), groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);

            if(g_found==false && equal == 0 ){
                g_found = true;

                short begin = (short)(i * GROUPNUMBERS_LENGTH);
                short end = (short)(begin + GROUPNUMBERS_LENGTH);

                for(short a=begin;a<end;a++)
                    //@ invariant begin <= a &*& a <= end;
                {
                    byte openplace = groupnbs[a];

                    if(added == false && openplace == 0){
                        JCSystem.beginTransaction();
                        added = true;

                        groupnbs[a] = contactnb;

                        JCSystem.commitTransaction();
                    }
                }
            }
        }

        if(g_found == false)
            ISOException.throwIt(SW_GROUP_NOT_FOUND);
        if(added == false)
            ISOException.throwIt(SW_GROUP_FULL);
    }

    private void removeContactFromGroup (APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() |-> ?abuffer &*& length(abuffer) >= ISO7816.OFFSET_LC + (NAME_LENGTH + GROUPNAME_LENGTH) &*& array_slice(abuffer, ISO7816.OFFSET_LC, 1, _) == [NAME_LENGTH + GROUPNAME_LENGTH];
        //@ requires phoneNbs != null &*& emptyPhoneNbs != null &*& length(phoneNbs) == 400 &*& length(emptyPhoneNbs) == 20 &*& groupnames != null &*& emptyGroups != null &*& groupnbs != null &*& length(groupnames) == 100 &*& length(emptyGroups) == 10 &*& length(groupnbs) == 100;
        //@ ensures groups_invariant(emptyGroups, groupnames, groupnbs) &*& phoneNbs_invariant(emptyPhoneNbs, phoneNbs);
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != (NAME_LENGTH + GROUPNAME_LENGTH))
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyPhoneNbs.length;

        boolean found = false;
        byte contactnb = 0;

        for(short i=0;i<length;i++)
            //@ invariant 0 <= i &*& i <= length;
        {
            short equal = Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH);

            if(found==false && equal == 0 ){
                found = true;

                contactnb = (byte)(short)(i+1);
            }
        }

        if(found == false)
            ISOException.throwIt(SW_PERSON_NOT_FOUND);

        short g_length = (short) emptyGroups.length;

        boolean g_found = false;

        for(short i=0;i<g_length;i++)
            //@ invariant 0 <= i &*& i <= g_length;
        {
            short equal = Util.arrayCompare(abuffer, (short)(ISO7816.OFFSET_CDATA + NAME_LENGTH), groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);

            if(g_found==false && equal == 0 ){
                g_found = true;

                short begin = (short)(i * GROUPNUMBERS_LENGTH);
                short end = (short)(begin + GROUPNUMBERS_LENGTH);

                for(short a=begin;a<end;a++)
                    //@ invariant begin <= a &*& a <= end;
                {
                    byte contactequal = groupnbs[a];

                    if(contactequal == contactnb){
                        JCSystem.beginTransaction();

                        groupnbs[a] = (byte)0;

                        JCSystem.commitTransaction();
                    }
                }
            }
        }

        if(g_found == false)
            ISOException.throwIt(SW_GROUP_NOT_FOUND);
    }

    private void deleteGroup (APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() |-> ?abuffer &*& length(abuffer) >= ISO7816.OFFSET_LC + GROUPNAME_LENGTH &*& array_slice(abuffer, ISO7816.OFFSET_LC, 1, _) == [GROUPNAME_LENGTH];
        //@ requires groupnames != null &*& emptyGroups != null &*& groupnbs != null &*& length(groupnames) == 100 &*& length(emptyGroups) == 10 &*& length(groupnbs) == 100;
        //@ ensures groups_invariant(emptyGroups, groupnames, groupnbs);
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != GROUPNAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyGroups.length;

        for(short i=0;i<length;i++)
            //@ invariant 0 <= i &*& i <= length &*& groups_invariant(emptyGroups, groupnames, groupnbs);
        {
            short item = emptyGroups[i];

            if(item == 1){
                short equal = (short)Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);

                if(equal == 0){
                    JCSystem.beginTransaction();

                    emptyGroups[i] = 0;

                    Util.arrayCopy(zeros,(short)0,groupnames,(short)(i * GROUPNAME_LENGTH),(short) GROUPNAME_LENGTH);

                    short begin = (short)(i * GROUPNUMBERS_LENGTH);
                    short end = (short)(begin + GROUPNUMBERS_LENGTH);

                    for(short a = begin; a < end; a++)
                        //@ invariant begin <= a &*& a <= end;
                    {
                        groupnbs[a] = (byte)0;
                    }

                    JCSystem.commitTransaction();
                }
            }
        }
    }

    private void searchInGroup (APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() |-> ?abuffer &*& length(abuffer) >= ISO7816.OFFSET_LC + (GROUPNAME_LENGTH + NAME_LENGTH) &*& array_slice(abuffer, ISO7816.OFFSET_LC, 1, _) == [GROUPNAME_LENGTH + NAME_LENGTH];
        //@ requires phoneNbs != null &*& emptyPhoneNbs != null &*& length(phoneNbs) == 400 &*& length(emptyPhoneNbs) == 20 &*& groupnames != null &*& emptyGroups != null &*& groupnbs != null &*& length(groupnames) == 100 &*& length(emptyGroups) == 10 &*& length(groupnbs) == 100;
        //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        if(abuffer[ISO7816.OFFSET_LC] != GROUPNAME_LENGTH + NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyGroups.length;

        boolean found = false;

        for(short i=0;i<length;i++)
            //@ invariant 0 <= i &*& i <= length;
        {
            short item = emptyGroups[i];

            if(item == 1){
                short equal = (short)Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);

                if(equal == 0){

                    short begin = (short)(i * GROUPNUMBERS_LENGTH);
                    short end = (short)(begin + GROUPNUMBERS_LENGTH);

                    for(short a=begin;a<end;a++)
                        //@ invariant begin <= a &*& a <= end;
                    {
                        byte contactnb = groupnbs[a];

                        if(contactnb > (byte)0 && found == false){

                            short same_name = (short)Util.arrayCompare(abuffer, (short)(ISO7816.OFFSET_CDATA + GROUPNAME_LENGTH), phoneNbs, (short)((contactnb-1) * RECORD_LENGTH), NAME_LENGTH);

                            if(same_name == 0){
                                found = true;
                                apdu.setOutgoing();
                                apdu.setOutgoingLength(NR_LENGTH);

                                apdu.sendBytesLong(phoneNbs, (short)(((contactnb-1) * RECORD_LENGTH) + NAME_LENGTH), NR_LENGTH);

                            }
                        }
                    }
                }
            }
        }
        if(found == false)
            ISOException.throwIt(SW_PERSON_NOT_FOUND);
    }

    private void filterContacts(APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() |-> ?abuffer &*& length(abuffer) >= ISO7816.OFFSET_LC + 1;
        //@ requires phoneNbs != null &*& emptyPhoneNbs != null &*& filteredNames != null &*& length(phoneNbs) == 400 &*& length(emptyPhoneNbs) == 20 &*& length(filteredNames) == 400;
        //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        short filterlength = (short)(abuffer[ISO7816.OFFSET_LC] & 0xff);
        if(filterlength > NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyPhoneNbs.length;

        boolean found = false;

        short index = (short)0;

        for(short i=0;i<length;i++)
            //@ invariant 0 <= i &*& i <= length;
        {
            short item = emptyPhoneNbs[i];

            if(item == 1){

                short compare = Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), filterlength);

                if(compare == 0){
                    found = true;
                    JCSystem.beginTransaction();

                    if(i > 0 && index < 19){
                        index++;
                    }

                    Util.arrayCopy(phoneNbs, (short)(i*RECORD_LENGTH), filteredNames,(short)(index * NAME_LENGTH), NAME_LENGTH);

                    JCSystem.commitTransaction();
                }
            }
        }

        if(found == false){
            ISOException.throwIt(SW_NO_PERSON_FOUND);
        }

        apdu.setOutgoing();

        apdu.setOutgoingLength((short)((index + 1)*NAME_LENGTH));

        for(short i=0;i<=index;i++)
            //@ invariant 0 <= i &*& i <= index + 1;
        {
            apdu.sendBytesLong(filteredNames, (short)(i*NAME_LENGTH), NAME_LENGTH);

        }
    }
}
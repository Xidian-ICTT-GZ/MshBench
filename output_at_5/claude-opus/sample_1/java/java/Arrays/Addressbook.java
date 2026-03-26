package Addressbook;

import javacard.framework.*;

public final class Addressbook extends Applet {

/*@
    predicate phoneNbs_array() = pointer(phoneNbs, ?len) &*& len == 400;
    predicate emptyPhoneNbs_array() = pointer(emptyPhoneNbs, ?len) &*& len == 20;
    predicate zeros_array() = pointer(zeros, ?len) &*& len == 20;
    predicate groupnames_array() = pointer(groupnames, ?len) &*& len == 100;
    predicate groupnbs_array() = pointer(groupnbs, ?len) &*& len == 100;
    predicate emptyGroups_array() = pointer(emptyGroups, ?len) &*& len == 10;
    predicate filteredNames_array() = pointer(filteredNames, ?len) &*& len == 400;
@*/

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

    public static void install(byte[] bArray, short bOffset, byte bLength)
    //@ requires true;
    //@ ensures true;
    {
        Addressbook addressbook = new Addressbook();
        addressbook.register();
    }

    protected Addressbook()
    //@ requires true;
    //@ ensures true;
    {
        phoneNbs = new byte[400];
        emptyPhoneNbs = new short[20];
        zeros = new byte[20];
        groupnames = new byte[100];
        groupnbs = new byte[100];
        emptyGroups = new short[10];
        filteredNames = new byte[400];

        for(short i = 0; i < 100; i++)
        //@ invariant 0 <= i && i <= 100;
        //@ decreases 100 - i;
        {
            groupnbs[i] = (byte)0;
        }
    }

    public void process(APDU apdu)
    //@ requires true;
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
    //@ requires true;
    //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != RECORD_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyPhoneNbs.length;
        boolean added = false;

        for(short i = 0; i < length; i++)
        //@ invariant 0 <= i && i <= length;
        //@ decreases length - i;
        {
            short item = emptyPhoneNbs[i];
            if(item == 0 && added == false){
                JCSystem.beginTransaction();
                added = true;
                emptyPhoneNbs[i] = 1;
                Util.arrayCopy(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), RECORD_LENGTH);
                JCSystem.commitTransaction();
            }
        }
        if(!added)
            ISOException.throwIt(SW_ADDRESSBOOK_FULL);
    }

    private void delete(APDU apdu)
    //@ requires true;
    //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyPhoneNbs.length;

        for(short i = 0; i < length; i++)
        //@ invariant 0 <= i && i <= length;
        //@ decreases length - i;
        {
            short item = emptyPhoneNbs[i];
            if(item == 1){
                short equal = (short)Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH);
                if(equal == 0){
                    JCSystem.beginTransaction();
                    emptyPhoneNbs[i] = 0;
                    Util.arrayCopy(zeros, (short)0, phoneNbs, (short)(i * RECORD_LENGTH), RECORD_LENGTH);
                    JCSystem.commitTransaction();
                }
            }
        }
    }

    private void search(APDU apdu)
    //@ requires true;
    //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyPhoneNbs.length;
        boolean found = false;

        for(short i = 0; i < length; i++)
        //@ invariant 0 <= i && i <= length;
        //@ decreases length - i;
        {
            short item = emptyPhoneNbs[i];
            if(item == 1 && found == false){
                if(Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH) == 0){
                    found = true;
                    apdu.setOutgoing();
                    apdu.setOutgoingLength(NR_LENGTH);
                    apdu.sendBytesLong(phoneNbs, (short)((i * RECORD_LENGTH) + NAME_LENGTH), NR_LENGTH);
                }
            }
        }
        if(found == false)
            ISOException.throwIt(SW_PERSON_NOT_FOUND);
    }

    private void addGroup(APDU apdu)
    //@ requires true;
    //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != GROUPNAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyGroups.length;
        boolean added = false;

        for(short i = 0; i < length; i++)
        //@ invariant 0 <= i && i <= length;
        //@ decreases length - i;
        {
            short item = emptyGroups[i];
            if(item == 0 && added == false){
                JCSystem.beginTransaction();
                added = true;
                emptyGroups[i] = 1;
                Util.arrayCopy(abuffer, (short)ISO7816.OFFSET_CDATA, groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);
                JCSystem.commitTransaction();
            }
        }
        if(added == false)
            ISOException.throwIt(SW_GROUPBOOK_FULL);
    }

    private void addContactToGroup(APDU apdu)
    //@ requires true;
    //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != (NAME_LENGTH + GROUPNAME_LENGTH))
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyPhoneNbs.length;
        boolean found = false;
        byte contactnb = 0;

        for(short i = 0; i < length; i++)
        //@ invariant 0 <= i && i <= length;
        //@ decreases length - i;
        {
            short equal = Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH);
            if(found == false && equal == 0){
                found = true;
                contactnb = (byte)(short)(i + 1);
            }
        }
        if(found == false)
            ISOException.throwIt(SW_PERSON_NOT_FOUND);

        short g_length = (short) emptyGroups.length;
        boolean g_found = false;
        boolean added = false;

        for(short i = 0; i < g_length; i++)
        //@ invariant 0 <= i && i <= g_length;
        //@ decreases g_length - i;
        {
            short equal = Util.arrayCompare(abuffer, (short)(ISO7816.OFFSET_CDATA + NAME_LENGTH), groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);
            if(g_found == false && equal == 0){
                g_found = true;

                short begin = (short)(i * GROUPNUMBERS_LENGTH);
                short end = (short)(begin + GROUPNUMBERS_LENGTH);

                for(short a = begin; a < end; a++)
                //@ invariant begin <= a && a <= end;
                //@ decreases end - a;
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

    private void removeContactFromGroup(APDU apdu)
    //@ requires true;
    //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != (NAME_LENGTH + GROUPNAME_LENGTH))
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyPhoneNbs.length;
        boolean found = false;
        byte contactnb = 0;

        for(short i = 0; i < length; i++)
        //@ invariant 0 <= i && i <= length;
        //@ decreases length - i;
        {
            short equal = Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH);
            if(found == false && equal == 0){
                found = true;
                contactnb = (byte)(short)(i + 1);
            }
        }
        if(found == false)
            ISOException.throwIt(SW_PERSON_NOT_FOUND);

        short g_length = (short) emptyGroups.length;
        boolean g_found = false;

        for(short i = 0; i < g_length; i++)
        //@ invariant 0 <= i && i <= g_length;
        //@ decreases g_length - i;
        {
            short equal = Util.arrayCompare(abuffer, (short)(ISO7816.OFFSET_CDATA + NAME_LENGTH), groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);
            if(g_found == false && equal == 0){
                g_found = true;

                short begin = (short)(i * GROUPNUMBERS_LENGTH);
                short end = (short)(begin + GROUPNUMBERS_LENGTH);

                for(short a = begin; a < end; a++)
                //@ invariant begin <= a && a <= end;
                //@ decreases end - a;
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

    private void deleteGroup(APDU apdu)
    //@ requires true;
    //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != GROUPNAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyGroups.length;

        for(short i = 0; i < length; i++)
        //@ invariant 0 <= i && i <= length;
        //@ decreases length - i;
        {
            short item = emptyGroups[i];
            if(item == 1){
                short equal = (short)Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);
                if(equal == 0){
                    JCSystem.beginTransaction();
                    emptyGroups[i] = 0;
                    Util.arrayCopy(zeros, (short)0, groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);
                    short begin = (short)(i * GROUPNUMBERS_LENGTH);
                    short end = (short)(begin + GROUPNUMBERS_LENGTH);
                    for(short a = begin; a < end; a++)
                    //@ invariant begin <= a && a <= end;
                    //@ decreases end - a;
                    {
                        groupnbs[a] = (byte)0;
                    }
                    JCSystem.commitTransaction();
                }
            }
        }
    }

    private void searchInGroup(APDU apdu)
    //@ requires true;
    //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        if(abuffer[ISO7816.OFFSET_LC] != GROUPNAME_LENGTH + NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyGroups.length;
        boolean found = false;

        for(short i = 0; i < length; i++)
        //@ invariant 0 <= i && i <= length;
        //@ decreases length - i;
        {
            short item = emptyGroups[i];
            if(item == 1){
                short equal = (short)Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);
                if(equal == 0){
                    short begin = (short)(i * GROUPNUMBERS_LENGTH);
                    short end = (short)(begin + GROUPNUMBERS_LENGTH);

                    for(short a = begin; a < end; a++)
                    //@ invariant begin <= a && a <= end;
                    //@ decreases end - a;
                    {
                        byte contactnb = groupnbs[a];
                        if(contactnb > (byte)0 && found == false){
                            short same_name = (short)Util.arrayCompare(abuffer, (short)(ISO7816.OFFSET_CDATA + GROUPNAME_LENGTH), phoneNbs, (short)((contactnb - 1) * RECORD_LENGTH), NAME_LENGTH);
                            if(same_name == 0){
                                found = true;
                                apdu.setOutgoing();
                                apdu.setOutgoingLength(NR_LENGTH);
                                apdu.sendBytesLong(phoneNbs, (short)(((contactnb - 1) * RECORD_LENGTH) + NAME_LENGTH), NR_LENGTH);
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
    //@ requires true;
    //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();

        short filterlength = (short)(abuffer[ISO7816.OFFSET_LC] & 0xff);
        if(filterlength > NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        short length = (short) emptyPhoneNbs.length;
        boolean found = false;

        short index = (short)0;

        for(short i = 0; i < length; i++)
        //@ invariant 0 <= i && i <= length;
        //@ decreases length - i;
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
                    Util.arrayCopy(phoneNbs, (short)(i * RECORD_LENGTH), filteredNames, (short)(index * NAME_LENGTH), NAME_LENGTH);
                    JCSystem.commitTransaction();
                }
            }
        }

        if(found == false)
            ISOException.throwIt(SW_NO_PERSON_FOUND);

        apdu.setOutgoing();
        apdu.setOutgoingLength((short)((index + 1) * NAME_LENGTH));

        for(short i = 0; i <= index; i++)
        //@ invariant 0 <= i && i <= index + 1;
        //@ decreases index + 1 - i;
        {
            apdu.sendBytesLong(filteredNames, (short)(i * NAME_LENGTH), NAME_LENGTH);
        }
    }
}
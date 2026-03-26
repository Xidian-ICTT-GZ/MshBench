package be.fedict.eidapplet;

import javacard.security.KeyPair;
import javacard.security.RSAPrivateKey;
import javacard.security.RSAPrivateCrtKey;
import javacard.security.RSAPublicKey;
import javacard.security.RandomData;
import javacardx.crypto.Cipher;
import org.globalplatform.GPSystem;

import javacard.framework.Applet;
import javacard.framework.*;
import javacard.security.PrivateKey;
import javacard.security.PublicKey;

public abstract class File {
	

	
	private short fileID;
	protected boolean active;
	
	//@ requires true;
	//@ ensures true;
	public File(short fid) 
    	{
		fileID = fid;
		active = true;
		
		
		
	}
	//@ requires true;
	//@ ensures true;
	public short getFileID() 
	{
		
		return fileID;
		
	}
	
	//@ requires true;
	//@ ensures true;
	public void setActive(boolean b)
	{
		
		active = b;
		
	}
	
	
	//@ requires true;
	//@ ensures true;
	public boolean isActive() 
	{
		
		return active;
		
	}
}

public class DedicatedFile extends File {

	

	

	
	private DedicatedFile parentFile;
	
	private static final byte MAX_SIBLINGS = 10;
	private File[] siblings;
	
	private byte number;
	
	//@ requires true;
	//@ ensures true;
	protected DedicatedFile(short fid) 
	{
		super(fid);
		parentFile = null;
		siblings = new File[MAX_SIBLINGS];
		number = 0;
		
		
	}
	//@ requires parent != null;
	//@ ensures true;
	public DedicatedFile(short fid, DedicatedFile parent) 
	{
		super(fid);
		parentFile = parent;
		siblings = new File[MAX_SIBLINGS];
		number = 0;
		parent.addSibling(this);
		
		
	}
	//@ requires true;
	//@ ensures true;
	public DedicatedFile getParent() 
	{
		
		return parentFile;
		
	}
	
	//@ requires true;
	//@ ensures true;
	protected void addSibling(File s) 
	{
                
		if (number < MAX_SIBLINGS) {
			
			siblings[number++] = s;
			
			
			
			
			
		}
		
		
		
		
	}

	//@ requires true;
	//@ ensures true;
	public File getSibling(short fid) 
	{
		
		
		
		for (byte i = 0; i < number; i++) 
		{
			File fl = siblings[i];
			
			
			if (fl != null && fl.getFileID() == fid) {
				
				return fl;
				
			}
			
		}
		
		return null;
	}

        
	//@ requires true;
	//@ ensures true;
	public short getFileID() 
	{
		
		File thiz = this;
		return fileID;
		
	}
	
	//@ requires true;
	//@ ensures true;
	public void setActive(boolean b)
	{
		
		
		File thiz = this;
		
		active = b;
		
		
		
	}
	
	//@ requires true;
	//@ ensures true;
	public boolean isActive() 
	{
		
		
		
		return active;
		
		
		
	}
	
	

}

public final class MasterFile extends DedicatedFile {
	
	
	

	private static final short MF_FID = 0x3F00;
	//@ requires true;
	//@ ensures true;
	public MasterFile() 
	{
		super(MF_FID);
		
	}
	
	
	//@ requires true;
	//@ ensures true;
	public DedicatedFile getParent() 
	{
		
		
		
		return parentFile;
		
		
		
	}

	
	//@ requires true;
	//@ ensures true;
	public File getSibling(short fid) 
	{
		
		
		return super.getSibling(fid);
		
		
	}
	
	
	//@ requires true;
	//@ ensures true;
	public short getFileID() 
	{
		
		return fileID;
		
	}
	
	//@ requires true;
	//@ ensures true;
	public void setActive(boolean b)
	{
		
		
		
		
		active = b;
		
		
		
		
	}
	
	//@ requires true;
	//@ ensures true;
	public boolean isActive() 
	{
		
		
		
		
		return active;
		
		
		
		
	}
	
	//@ requires true;
	//@ ensures true;
	protected void addSibling(File s) 
 	{
		
		
		
		super.addSibling(s);
		
		
	}
	
	

}

public final class ElementaryFile extends File {
	

	

		
	
	private DedicatedFile parentFile;
	
	private byte[] data;
	
	short size;
	//@ requires parent != null && d != null;
	//@ ensures true;
	public ElementaryFile(short fid, DedicatedFile parent, byte[] d) 
	{
		super(fid);
		parentFile = parent;
		parent.addSibling(this);
		data = d;
		size = (short) d.length;
		
	}
	//@ requires parent != null;
	//@ ensures true;
	public ElementaryFile(short fid, DedicatedFile parent, short maxSize) 
	{
		super(fid);
		parentFile = parent;
		parent.addSibling(this);
		data = new byte[maxSize];
		size = (short) 0;
		
		
	}
	//@ requires true;
	//@ ensures true;
	public byte[] getData() 
	{
		if (active == true) {
			return data;
		} else {
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
			
			return null; 
		}
	}
	//@ requires true;
	//@ ensures true;
	public short getCurrentSize() 
	{	
		
		
		if (active == true) {
			return size;
			
			
		} else {
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		}
	}
	//@ requires true;
	//@ ensures true;
	public short getMaxSize() 
	{
		
		return (short) this.data.length;
		
	}
	//@ requires true;
	//@ ensures true;
	public void eraseData(short offset) 
	{
		
		Util.arrayFillNonAtomic(data, offset, (short)(size - offset), (byte) 0);
		
	}
	//@ requires newData != null;
	//@ ensures true;
	public void updateData(short dataOffset, byte[] newData, short newDataOffset, short length) 
	{
		
		
		size = (short) (dataOffset + length);
		
		Util.arrayCopy(newData, newDataOffset, data, dataOffset, length);
		
	}

	
	//@ requires true;
	//@ ensures true;
	public short getFileID() 
	{
		
		return fileID;
		
	}
	
	
	//@ requires true;
	//@ ensures true;
	public void setActive(boolean b)
	{
		
		
		super.setActive(b);
		
		
	}
	
	
	//@ requires true;
	//@ ensures true;
	public boolean isActive() 
	{
		
		
		boolean b = super.isActive();
		
		
		return b;
	}
	
	

}

public final class EidCard extends Applet {
	

	
	
	private final static byte EIDCARD_CLA_2 = (byte) 0x80;
	private final static byte EIDCARD_CLA_1 = (byte) 0x00;
	
	private final static byte INS_GET_RESPONSE = (byte) 0xC0;
	private final static byte INS_SELECT_FILE = (byte) 0xA4;
	private final static byte INS_ACTIVATE_FILE = (byte) 0x44;
	private final static byte INS_DEACTIVATE_FILE = (byte) 0x04;
	private final static byte INS_READ_BINARY = (byte) 0xB0;
	private final static byte INS_UPDATE_BINARY = (byte) 0xD6;
	private final static byte INS_ERASE_BINARY = (byte) 0x0E;
	private final static byte INS_VERIFY_PIN = (byte) 0x20;
	private final static byte INS_CHANGE_PIN = (byte) 0x24;
	private final static byte INS_UNBLOCK = (byte) 0x2C;
	private final static byte INS_GET_CHALLENGE = (byte) 0x84;
	private final static byte INS_INTERNAL_AUTHENTICATE = (byte) 0x88;

	private final static byte INS_EXTERNAL_AUTHENTICATE = (byte) 0x82;

	private final static byte INS_ENVELOPE = (byte) 0xC2;
	private final static byte INS_PREPARE_SIGNATURE = (byte) 0x22;
	private final static byte INS_GENERATE_SIGNATURE = (byte) 0x2A;
	private final static byte INS_GENERATE_KEYPAIR = (byte) 0x46;
	private final static byte INS_GET_KEY = (byte) 0xE2;
	private final static byte INS_PUT_KEY = (byte) 0xF2;
	private final static byte INS_ERASE_KEY = (byte) 0xF4;
	private final static byte INS_ACTIVATE_KEY = (byte) 0xF6;
	private final static byte INS_DEACTIVATE_KEY = (byte) 0xF8;
	private final static byte INS_GET_CARD_DATA = (byte) 0xE4;
	private final static byte INS_LOG_OFF = (byte) 0xE6;
	private final static byte INS_BLOCK = (byte) 0xE8;
	private byte[] previousApduType; 
	
	
	private final static byte VERIFY_CARDHOLDER_PIN = (byte) 0x01;
	
	private final static byte VERIFY_RESET_PIN = (byte) 0x02;
	private final static byte GENERATE_KEY_PAIR = (byte) 0x03;
	private final static byte OTHER = (byte) 0x00;
	
	

	private final static short SW_CANCELLED = (short) 0xFFFF;
	private final static short SW_ALGORITHM_NOT_SUPPORTED = (short) 0x9484;
	
	
	private final static short SW_WRONG_PIN_0_TRIES_LEFT = (short) 0x63C0;
	private final static short SW_INCONSISTENT_P1P2 = (short) 0x6A87;
	private final static short SW_REFERENCE_DATA_NOT_FOUND = (short) 0x6A88;
	
	private final static short SW_WRONG_LENGTH_00 = (short) 0x6C00;
	
	
	private final static byte OFFSET_PIN_HEADER = ISO7816.OFFSET_CDATA;
	private final static byte OFFSET_PIN_DATA = ISO7816.OFFSET_CDATA + 1;
	
	private final static byte OFFSET_SECOND_PIN_HEADER = ISO7816.OFFSET_CDATA + 8;

	private final static byte OFFSET_SECOND_PIN_DATA = ISO7816.OFFSET_CDATA + 9;

	private final static byte OFFSET_SECOND_PIN_DATA_END = ISO7816.OFFSET_CDATA + 15;
	
	protected final static byte PIN_SIZE = 8;
	protected final static byte CARDHOLDER_PIN = (byte) 0x01;
	protected final static byte CARDHOLDER_PIN_TRY_LIMIT = 3;
	protected final static byte RESET_PIN = (byte) 0x02;
	protected final static byte RESET_PIN_TRY_LIMIT = 10;
	protected final static byte UNBLOCK_PIN = (byte) 0x03;
	protected final static byte UNBLOCK_PIN_TRY_LIMIT = 12;
	protected final static byte ACTIVATE_PIN = (byte) 0x84;
	protected final static byte ACTIVATE_PIN_TRY_LIMIT = 15;
	protected OwnerPIN cardholderPin;
	protected OwnerPIN resetPin;
	protected OwnerPIN unblockPin;
	protected OwnerPIN activationPin;
	
	
	
	
	private byte signatureAlgorithm;
	private final static byte ALG_PKCS1 = (byte) 0x01;
	private final static byte ALG_SHA1_PKCS1 = (byte) 0x02;
	private final static byte ALG_MD5_PKCS1 = (byte) 0x04;
	private final static byte[] PKCS1_HEADER = { (byte) 0x00 };
	private final static byte[] PKCS1_SHA1_HEADER = { 0x00, (byte) 0x30, (byte) 0x21, (byte) 0x30, (byte) 0x09, (byte) 0x06, (byte) 0x05, (byte) 0x2b, (byte) 0x0e, (byte) 0x03, (byte) 0x02, (byte) 0x1a, (byte) 0x05, (byte) 0x00, (byte) 0x04,
			(byte) 0x14 };
	private final static byte[] PKCS1_MD5_HEADER = { (byte) 0x00, (byte) 0x30, (byte) 0x20, (byte) 0x30, (byte) 0x0c, (byte) 0x06, (byte) 0x08, (byte) 0x2a, (byte) 0x86, (byte) 0x48, (byte) 0x86, (byte) 0xf7, (byte) 0x0d, (byte) 0x02, (byte) 0x05,
			(byte) 0x05, (byte) 0x00, (byte) 0x04, (byte) 0x10 };
	private byte[] signatureType; 
	private final static byte NO_SIGNATURE = (byte) 0x00;
	private final static byte BASIC = (byte) 0x81;
	private final static byte AUTHENTICATION = (byte) 0x82;
	private final static byte NON_REPUDIATION = (byte) 0x83;
	private final static byte CA_ROLE = (byte) 0x87;
	
	
	protected static KeyPair basicKeyPair;
	protected static KeyPair authKeyPair;
	protected static KeyPair nonRepKeyPair;
	
	
	
	
	
	private static Cipher cipher;
	private static RandomData randomData;
	
	private static byte[] messageBuffer;
	

	protected final static short MF = (short) 0x3F00;
	protected final static short EF_DIR = (short) 0x2F00;
	protected final static short DF_BELPIC = (short) 0xDF00;
	protected final static short DF_ID = (short) 0xDF01;
	protected MasterFile masterFile;
	protected DedicatedFile belpicDirectory, idDirectory;
	protected ElementaryFile dirFile;
	
	protected final static short ODF = (short) 0x5031;
	protected final static short TOKENINFO = (short) 0x5032;
	protected final static short AODF = (short) 0x5034;
	protected final static short PRKDF = (short) 0x5035;
	protected final static short CDF = (short) 0x5037;
	protected final static short AUTH_CERTIFICATE = (short) 0x5038;
	protected final static short NONREP_CERTIFICATE = (short) 0x5039;
	protected final static short CA_CERTIFICATE = (short) 0x503A;
	protected final static short ROOT_CA_CERTIFICATE = (short) 0x503B;
	protected final static short RRN_CERTIFICATE = (short) 0x503C;
	protected ElementaryFile objectDirectoryFile, tokenInfo, authenticationObjectDirectoryFile, privateKeyDirectoryFile, certificateDirectoryFile, authenticationCertificate, nonRepudiationCertificate, caCertificate, rootCaCertificate, rrnCertificate;
	
	protected final static short IDENTITY = (short) 0x4031;
	protected final static short SGN_IDENTITY = (short) 0x4032;
	protected final static short ADDRESS = (short) 0x4033;
	protected final static short SGN_ADDRESS = (short) 0x4034;
	protected final static short PHOTO = (short) 0x4035;
	protected final static short CA_ROLE_ID = (short) 0x4038;
	protected final static short PREFERENCES = (short) 0x4039;
	protected ElementaryFile identityFile, identityFileSignature, addressFile, addressFileSignature, photoFile, caRoleIDFile, preferencesFile;

	

	
	private final static byte READ_BINARY = (byte) 0x01;

	private final static byte SEARCH_BINARY = (byte) 0x01;
	private final static byte UPDATE_BINARY = (byte) 0x02;
	private final static byte ERASE_BINARY = (byte) 0x02;

	private final static byte WRITE_BINARY = (byte) 0x04;
	

	private final static byte DELETE_CHILD_FILE = (byte) 0x01;

	private final static byte CREATE_EF = (byte) 0x02;

	private final static byte CREATE_DF = (byte) 0x04;
	

	private final static byte DEACTIVATE_FILE = (byte) 0x08;

	private final static byte ACTIVATE_FILE = (byte) 0x10;

	private final static byte TERMINATE_FILE = (byte) 0x20;

	private final static byte DELETE_FILE = (byte) 0x40;
	
	
	private byte[] randomBuffer;
	
	private byte[] responseBuffer;
	
	private File selectedFile;
	
	
	private short internalAuthenticateCounter = 5000;
	

	//@ requires true;
	//@ ensures true;
	public static void install(byte[] bArray, short bOffset, byte bLength) 
	{
		
		new EidCard();
	}
	
	

	//@ requires true;
	//@ ensures true;
	private void initializeFileSystem() 
	{
		masterFile = new MasterFile();
		

		
		
		
		dirFile = new ElementaryFile(EF_DIR, masterFile, (short) 0x25);
		belpicDirectory = new DedicatedFile(DF_BELPIC, masterFile);
		tokenInfo = new ElementaryFile(TOKENINFO, belpicDirectory, (short) 0x30);
		objectDirectoryFile = new ElementaryFile(ODF, belpicDirectory, (short) 40);
		authenticationObjectDirectoryFile = new ElementaryFile(AODF, belpicDirectory, (short) 0x40);
		privateKeyDirectoryFile = new ElementaryFile(PRKDF, belpicDirectory, (short) 0xB0);
		certificateDirectoryFile = new ElementaryFile(CDF, belpicDirectory, (short) 0xB0);
		idDirectory = new DedicatedFile(DF_ID, masterFile);
		

		
		identityFile = new ElementaryFile(IDENTITY, idDirectory, (short) 0xD0);
		
		identityFileSignature = new ElementaryFile(SGN_IDENTITY, idDirectory, (short) 0x80);
		
		
		addressFile = new ElementaryFile(ADDRESS, idDirectory, (short) 117);
		
		addressFileSignature = new ElementaryFile(SGN_ADDRESS, idDirectory, (short) 128);
		
		caRoleIDFile = new ElementaryFile(CA_ROLE_ID, idDirectory, (short) 0x20);
		
		preferencesFile = new ElementaryFile(PREFERENCES, idDirectory, (short) 100);
		
		selectedFile = masterFile;
		
	}
	
	

	//@ requires apdu != null && buffer != null;
	//@ ensures true;
	private void eraseBinary(APDU apdu, byte[] buffer) 
	{
		
		if (!fileAccessAllowed(ERASE_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		
		short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
		JCSystem.beginTransaction();
		
		if (selectedFile == masterFile)
			ISOException.throwIt(ISO7816.SW_FILE_INVALID); 
		
		
		short size = ((ElementaryFile)selectedFile).getCurrentSize();
		
		if (offset > size || offset < 0)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		((ElementaryFile) selectedFile).eraseData(offset);
		
		JCSystem.commitTransaction();
	}
	

	//@ requires apdu != null && buffer != null;
	//@ ensures true;
	private void updateBinary(APDU apdu, byte[] buffer) 
	{
		
		if (!fileAccessAllowed(UPDATE_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		
		short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
		
		
		JCSystem.beginTransaction();
		
		if (selectedFile == masterFile)
			ISOException.throwIt(ISO7816.SW_FILE_INVALID); 
		
		short size = ((ElementaryFile) selectedFile).getMaxSize();
		if (offset > size)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		
		
		short byteRead = apdu.setIncomingAndReceive();
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc == 0) || (byteRead == 0))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		if (offset < 0 || ISO7816.OFFSET_CDATA + lc > buffer.length || offset + lc > size)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		((ElementaryFile) selectedFile).updateData(offset, buffer, ISO7816.OFFSET_CDATA, lc);
		
		JCSystem.commitTransaction();
	}
	

	//@ requires true;
	//@ ensures true;
	private boolean fileAccessAllowed(byte mode) 
	{
			
		if (!(selectedFile instanceof ElementaryFile))
			ISOException.throwIt(ISO7816.SW_COMMAND_NOT_ALLOWED);
		
		if (mode == READ_BINARY) {
				return true;
		}
		
		
		if ((selectedFile == preferencesFile) && cardholderPin.isValidated()) {
				return true;
		}
		
		
		if (GPSystem.getCardContentState() == GPSystem.APPLICATION_SELECTABLE) {
				return true;			
		}
			
		return false;
	}
	

	//@ requires apdu != null && buffer != null;
	//@ ensures true;
	private void getCardData(APDU apdu, byte[] buffer) 
	{
		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00 || buffer[ISO7816.OFFSET_P2] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		
		apdu.setOutgoing();
		
		
								
		byte[] data = identityFile.getData(); 
		
		short pos = 1;
		
		short dataLen = (short) data[pos];
		pos = (short) (pos + 1 + dataLen + 1);
		
		if (dataLen <= 0 || dataLen + pos + 2 >= identityFile.getCurrentSize())
			ISOException.throwIt(ISO7816.SW_DATA_INVALID);
		
		dataLen = (short) data[pos];
		pos = (short) (pos + 1);
		
		if (dataLen < 0 || pos + dataLen >= identityFile.getCurrentSize())
			ISOException.throwIt(ISO7816.SW_DATA_INVALID);
		
		
		
		
		
		byte version[] = new byte[] { (byte) 0xA5, (byte) 0x03, (byte) 0x01, (byte) 0x01, (byte) 0x01, (byte) 0x11, (byte) 0x00, (byte) 0x02, (byte) 0x00, (byte) 0x01, (byte) 0x01, (byte) 0x0F };
		byte chipNumber[] = new byte[(short) (dataLen + 12)];
		Util.arrayCopy(data, pos, chipNumber, (short) 0, dataLen);
		Util.arrayCopy(version, (short) 0, chipNumber, dataLen, (short) 12);
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		apdu.setOutgoingLength((short) chipNumber.length);
		
		apdu.sendBytesLong(chipNumber, (short) 0, (short) chipNumber.length);
								
		
		
	}
	
	

	//@ requires apdu != null && buffer != null;
	//@ ensures true;
	private void readBinary(APDU apdu, byte[] buffer) 
	{
		
		
		if (!fileAccessAllowed(READ_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		
		short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
		if (offset < 0)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		
		short le = apdu.setOutgoing();
		
		if (selectedFile == masterFile)
			ISOException.throwIt(ISO7816.SW_FILE_INVALID); 
		
		short size = ((ElementaryFile) selectedFile).getCurrentSize();
		if (offset > size)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		short remaining = (short) (size - offset);
		if (le == 0) {
			if (remaining < 256) {
				
				
				short sw = (short) (ISO7816.SW_CORRECT_LENGTH_00 | remaining);
				ISOException.throwIt(sw);
			} else
				
				le = 256;
		}
		
		if (le > remaining) {
			le = remaining;
		}
		
		apdu.setOutgoingLength(le);
		
		
		
		
		
		
		
		
		ElementaryFile ef = (ElementaryFile)selectedFile;
		byte[] bf = ef.getData();
		
		apdu.sendBytesLong(bf, offset, le);
		
		
	}
	
	

	//@ requires apdu != null && buffer != null;
	//@ ensures true;
	private void activateFile(APDU apdu, byte[] buffer) 
	{
		
		if (buffer[ISO7816.OFFSET_P2] != (byte) 0x0C)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		switch (buffer[ISO7816.OFFSET_P1]) {
		case (byte) 0x02:
			selectByFileIdentifier(apdu, buffer);
			break;
		case (byte) 0x08:
			selectByPath(apdu, buffer);
			break;
		default:
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
			break; 
		}
		
		if (!fileAccessAllowed(UPDATE_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		JCSystem.beginTransaction();
		
		
		
		selectedFile.setActive(true);
		
		
		JCSystem.commitTransaction();
	}	
	
	
	static byte[] dirData;
	static byte[] tokenInfoData;
	static byte[] odfData;
	static byte[] aodfData;
	static byte[] prkdfData;
	static byte[] cdfData;
	static byte[] citizenCaCert;
	static byte[] rrnCert;
	static byte[] rootCaCert;
	static byte[] photoData;  
	
	

	//@ requires true;
	//@ ensures true;
	private void clear() 
	{
		JCSystem.beginTransaction();
		
		

		
		Util.arrayFillNonAtomic(randomBuffer, (short) 0, (short) 256, (byte) 0);
		Util.arrayFillNonAtomic(responseBuffer, (short) 0, (short) 128, (byte) 0);
		
		selectedFile = masterFile;
		
		cardholderPin.reset();
		

		
		

		JCSystem.commitTransaction();
	}
	

	//@ requires true;
	//@ ensures true;
	private void initializeEmptyLargeFiles() 
	{
		

		caCertificate = new ElementaryFile(CA_CERTIFICATE, belpicDirectory, (short) 1200);
		rrnCertificate = new ElementaryFile(RRN_CERTIFICATE, belpicDirectory, (short) 1200);
		
		rootCaCertificate = new ElementaryFile(ROOT_CA_CERTIFICATE, belpicDirectory, (short) 1200);
		

		photoFile = new ElementaryFile(PHOTO, idDirectory, (short) 3584);
		

		authenticationCertificate = new ElementaryFile(AUTH_CERTIFICATE, belpicDirectory, (short) 1200);
		nonRepudiationCertificate = new ElementaryFile(NONREP_CERTIFICATE, belpicDirectory, (short) 1200);
	}
	
	

	//@ requires true;
	//@ ensures true;
	private void initializeKeyPairs() 
	{
		

		if (EidCard.basicKeyPair != null && authKeyPair != null && nonRepKeyPair != null) {
			return;
		}
		
		
		basicKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) 1
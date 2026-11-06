import java.nio.ByteBuffer;

/** Java rewrite of BINCNT.cob: the record is the 8 bytes of WS-REC (big-endian, as on z/OS). */
public final class BinCnt {
    public static void update(byte[] rec) {
        ByteBuffer bb = ByteBuffer.wrap(rec);      // big-endian by default
        short cnt = bb.getShort(0);
        int total = bb.getInt(2);
        cnt++;                                     // wraps at 32767, like COMP-5
        total = total + cnt * 3;                   // short promoted to int; int wrap-around
        bb.putShort(0, cnt);
        bb.putInt(2, total);
        rec[6] = rec[2];                           // MOVE WS-HI TO WS-OUT
        rec[7] = rec[3];
    }
}

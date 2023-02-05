public final class FileReader {
  /*@ ghost public static final int STATE_INIT = 1;*/
  /*@ ghost public static final int STATE_OPENED = 2;*/
  /*@ ghost public static final int STATE_CLOSED = 3;*/

  /*@ ghost private spec_public int state;*/
  private /*@ spec_public @*/ int remaining;

  /*@ public model \locset footprint;
    @ accessible footprint: \nothing;
    @ represents footprint = state, remaining;
    @*/

  /*@ invariant remaining >= 0; @*/

  /*@
    @ normal_behavior
    @ assignable \nothing;
    @ ensures state == STATE_INIT;
    @ ensures \fresh(footprint);
    @ ensures !(\exists FileReader f; this != f && \fresh(f));
    @*/
  public FileReader() {
    /*@ set state = STATE_INIT;*/
  }

  /*@
    @ normal_behavior
    @ requires state == STATE_INIT;
    @ assignable footprint;
    @ ensures state == STATE_OPENED;
    @ ensures !(\exists FileReader f; \fresh(f));
    @*/
  public void open() {
    this.remaining = 20;
    /*@ set state = STATE_OPENED;*/
  }

  /*@
    @ normal_behavior
    @ requires state == STATE_OPENED && remaining != 0;
    @ assignable footprint;
    @ ensures state == STATE_OPENED && remaining == \old(remaining) - 1;
    @ ensures !(\exists FileReader f; \fresh(f));
    @*/
  public byte read() {
    this.remaining--;
    return 0;
  }

  /*@
    @ normal_behavior
    @ requires state == STATE_OPENED;
    @ ensures state == STATE_OPENED && \result == (remaining == 0);
    @ ensures !(\exists FileReader f; \fresh(f));
    @*/
  public /*@ pure */ boolean eof() {
    return this.remaining == 0;
  }

  /*@
    @ normal_behavior
    @ requires state == STATE_OPENED && remaining == 0;
    @ assignable footprint;
    @ ensures state == STATE_CLOSED && remaining == 0;
    @ ensures !(\exists FileReader f; \fresh(f));
    @*/
  public void close() {
    /*@ set state = STATE_CLOSED;*/
  }
}

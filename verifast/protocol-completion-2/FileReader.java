/*@
predicate filereader(FileReader file; int state, int remaining) =
  file.state |-> state &*& file.remaining |-> remaining &*& remaining >= 0;
@*/

public class FileReader {
  public static final int STATE_INIT = 1;
  public static final int STATE_OPENED = 2;
  public static final int STATE_EOF = 3;
  public static final int STATE_CLOSED = 4;

  private int state;
  private int remaining;

  public FileReader(String filename)
    //@ requires tracker(?n);
    //@ ensures tracker(n + 1) &*& filereader(this, STATE_INIT, _);
  {
    this.state = STATE_INIT;
    //@ increment_tracker();
  }

  public void open()
    //@ requires filereader(this, STATE_INIT, _);
    //@ ensures filereader(this, STATE_OPENED, _);
  {
    this.remaining = 20;
    this.state = STATE_OPENED;
  }

  public byte read()
    //@ requires filereader(this, STATE_OPENED, ?r) &*& r > 0;
    //@ ensures filereader(this, STATE_OPENED, r - 1);
  {
    this.remaining--;
    return 0;
  }

  public boolean eof()
    //@ requires filereader(this, STATE_OPENED, ?r);
    //@ ensures filereader(this, STATE_OPENED, r) &*& (result == (r == 0));
  {
    return this.remaining == 0;
  }

  public void close()
    //@ requires tracker(?n) &*& filereader(this, STATE_OPENED, 0);
    //@ ensures tracker(n - 1) &*& filereader(this, STATE_CLOSED, 0);
  {
    this.state = STATE_CLOSED;
    //@ decrement_tracker();
  }

  public static void main(String[] args)
    //@ requires tracker(0);
    //@ ensures tracker(0);
  {
    FileReader f = new FileReader("file.txt");
    f.open();
    while (!f.eof())
      //@ invariant filereader(f, STATE_OPENED, ?r);
    {
      // This open is needed to prove that remaining > 0
      //@ open filereader(_, _, _);
      f.read();
    }
    f.close();
  }
}

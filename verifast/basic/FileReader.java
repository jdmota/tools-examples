/*@
predicate filereader(FileReader file; int s, int r) =
  file.state |-> s &*& file.remaining |-> r &*& r >= 0;
@*/

public class FileReader {
  public static final int STATE_INIT = 1;
  public static final int STATE_OPENED = 2;
  public static final int STATE_CLOSED = 3;

  private int state;
  private int remaining;

  public FileReader(String filename)
    //@ requires true;
    //@ ensures filereader(this, STATE_INIT, _);
  {
    this.state = STATE_INIT;
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
    //@ requires filereader(this, STATE_OPENED, 0);
    //@ ensures filereader(this, STATE_CLOSED, 0);
  {
    this.state = STATE_CLOSED;
  }
  
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
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

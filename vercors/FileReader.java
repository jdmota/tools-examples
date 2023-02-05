public class FileReader {
  //@ ghost private int state;
  private int remaining;

  //@ given FileTracker tracker;
  //@ context Perm(tracker.active, 1);
  //@ ensures Perm(state, 1) ** Perm(remaining, 1) ** state == 1 ** remaining >= 0;
  //@ ensures tracker.active == \old(tracker.active) + 1;
  public FileReader() {
    this.remaining = 0;
    //@ ghost this.state = 1;
    //@ ghost tracker.inc();
  }

  //@ context Perm(state, 1) ** Perm(remaining, 1) ** remaining >= 0;
  //@ requires state == 1;
  //@ ensures state == 2;
  public void open() {
    this.remaining = 20;
    //@ ghost this.state = 2;
  }

  //@ context Perm(state, 1) ** Perm(remaining, 1) ** remaining >= 0;
  //@ requires state == 2 ** remaining > 0;
  //@ ensures state == 2 ** remaining == \old(remaining) - 1;
  public int read() {
    this.remaining--;
    return 0;
  }

  //@ context Perm(state, 1) ** Perm(remaining, 1) ** remaining >= 0;
  //@ requires state == 2;
  //@ ensures state == 2 ** \result == (remaining == 0);
  public boolean eof() {
    return this.remaining == 0;
  }

  //@ given FileTracker tracker;
  //@ context Perm(tracker.active, 1);
  //@ context Perm(state, 1) ** Perm(remaining, 1) ** remaining >= 0;
  //@ requires state == 2 ** remaining == 0;
  //@ ensures state == 3;
  //@ ensures tracker.active == \old(tracker.active) - 1;
  public void close() {
    //@ ghost this.state = 3;
    //@ ghost tracker.dec();
  }

  //@ given FileTracker tracker;
  //@ context Perm(tracker.active, 1);
  //@ requires tracker.active == 0;
  //@ ensures tracker.active == 0;
  public static void main(String[] args) {
    FileReader f = new FileReader() /*@ with {tracker=tracker;} @*/;
    f.open();
    // Workaround https://github.com/utwente-fmt/vercors/issues/436
    boolean end = f.eof();
    //@ loop_invariant Perm(f.state, 1) ** Perm(f.remaining, 1) ** f.state == 2 ** f.remaining >= 0 ** (end == (f.remaining == 0));
    while (!end) {
      f.read();
      end = f.eof();
    }
    f.close() /*@ with {tracker=tracker;} @*/;
  }
}

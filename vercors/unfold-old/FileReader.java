public class FileReader {
  //@ ghost private int state;
  private int remaining;

  //@ ensures Perm(state, 1) ** Perm(remaining, 1) ** state == 1 ** remaining >= 0;
  public FileReader() {
    //@ ghost this.state = 1;
    this.remaining = 20;
  }

  //@ context Perm(state, 1) ** Perm(remaining, 1) ** remaining >= 0;
  //@ requires state == 1;
  //@ ensures state == 2 ** remaining == \old(remaining);
  public boolean open() {
    //@ ghost this.state = 2;
    return true;
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

  //@ context Perm(state, 1) ** Perm(remaining, 1) ** remaining >= 0;
  //@ requires state == 2 ** remaining == 0;
  //@ ensures state == 3;
  public void close() {
    //@ ghost this.state = 3;
  }
}

public class FileReader {
  private int remaining;

  // states init, opened, closed refine alive;
  // states eof, notEof refine opened;

  // eof := remaining == 0;
  // notEof := remaining > 0;

  public FileReader(String filename)
    // 1 -o unique(this) in init
  {
    this.remaining = 20;
  }

  public boolean open()
    // full(this) in init -o full(this) in opened
  {
    return true;
  }

  public byte read()
    // full(this) in notEof -o full(this) in opened
  {
    this.remaining--;
    return 0;
  }

  public boolean eof()
    // pure(this) in opened -o
    //     (result == true && pure(this) in eof) ||
    //     (result == false && pure(this) in notEof)
  {
    return this.remaining == 0;
  }

  public void close()
    // full(this) in eof -o full(this) in closed
  {

  }
}

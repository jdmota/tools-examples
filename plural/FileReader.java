import edu.cmu.cs.plural.annot.Perm;
import edu.cmu.cs.plural.annot.States;

@States(value={"init", "opened", "closed"}, refine="alive")
@States(value={"eof", "notEof"}, refine="opened")
@ClassStates({
  @State(name="eof", inv="remaining == 0"),
  @State(name="notEof", inv="remaining != 0")
})
public class FileReader {
  private int remaining;

  @Perm(requires="one", ensures="unique(this) in init")
  public FileReader(String filename) {
    this.remaining = 20;
  }

  @Perm(requires="full(this) in init", ensures="full(this) in opened")
  public boolean open() {
    return true;
  }

  @Perm(requires="full(this) in notEof", ensures="full(this) in opened")
  public byte read() {
    this.remaining--;
    return 0;
  }

  @Perm(
    requires="pure(this) in opened",
    ensures="(result == true * pure(this) in eof) + (result == false * pure(this) in notEof)"
  )
  public boolean eof() {
    return this.remaining == 0;
  }

  @Perm(requires="full(this) in eof", ensures="full(this) in closed")
  public void close() {

  }
}

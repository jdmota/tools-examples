import edu.cmu.cs.plural.annot.*;

@Refine({
  @States(value={"init", "opened", "closed"}, refined="alive"),
  @States(value={"eof", "notEof"}, refine="opened")
})
@ClassStates({
  @State(name="eof", inv="remaining == 0"),
  @State(name="notEof", inv="remaining > 0")
})
public class FileReader {
  private int remaining;

  @Perm(ensures="unique(this!fr) in init")
  public FileReader(String filename) {
    this.remaining = 20;
  }

  @Full(requires="init", ensures="opened")
  public boolean open() {
    return true;
  }

  @Full(requires="notEof", ensures="opened")
  public byte read() {
    this.remaining--;
    return 0;
  }

  @Imm(guarantee="opened")
  @TrueIndicates("eof")
  @FalseIndicates("notEof")
  public boolean eof() {
    return this.remaining == 0;
  }

  @Full(requires="eof", ensures="closed")
  public void close() {

  }
}

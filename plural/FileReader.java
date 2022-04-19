import edu.cmu.cs.plural.annot.*;

@Refine({
  @States(value={"init", "opened", "closed"}, refined="alive"),
  @States(value={"eof", "notEof"}, refined="opened")
})
@ClassStates({
  @State(name="init", inv="opened == false * closed == false"),
  @State(name="opened", inv="opened == true * closed == false"),
  @State(name="eof", inv="remaining == false"),
  @State(name="notEof", inv="remaining == true"),
  @State(name="closed", inv="opened == true * closed == true")
})
public class FileReader {
  private boolean remaining;
  private boolean opened, closed;

  @Perm(ensures="unique(this!fr) in init")
  public FileReader() {
    remaining = true;
    opened = false;
    closed = false;
  }

  @Unique(requires="init", ensures="opened", use=Use.FIELDS)
  public void open() {
    opened = true;
  }

  @Unique(requires="notEof", ensures="opened", use=Use.FIELDS)
  public byte read() {
    remaining = false;
    return 0;
  }

  @Imm(guarantee="opened", use=Use.FIELDS)
  @TrueIndicates("eof")
  @FalseIndicates("notEof")
  public boolean eof() {
    if (remaining == false) {
      return true;
    }
    return false;
  }

  @Unique(requires="eof", ensures="closed", use=Use.FIELDS)
  public void close() {
    closed = true;
  }
  
  public static void okExample() {
    FileReader f = new FileReader();
    f.open();
    while (!f.eof()) {
      f.read();
    }
    f.close();
  }
  
  public static void notOkExample() {
    FileReader f = new FileReader();
    f.open();
    while (f.eof()) {
      f.read(); // expected error: argument this must be in state [notEof] but is in [eof]
    }
    f.close(); // expected error: argument this must be in state [eof] but is in [notEof]
  }

  public static void droppingObject(@Unique(requires="opened", returned=false) FileReader f) {

  }
}

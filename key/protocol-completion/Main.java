public class Main {
  /*@
    @ normal_behavior
    @ requires !(\exists FileReader f; true);
    @ ensures (\forall FileReader f; f.state == FileReader.STATE_CLOSED);
    @*/
  public static void main(String[] args) {
    FileReader f1 = new FileReader();
    FileReader f2 = new FileReader();
    FileReader f3 = new FileReader();
    use(f1);
    use(f2);
    use(f3);
  }

  /*@
    @ normal_behavior
    @ requires \invariant_for(f);
    @ requires f.state == FileReader.STATE_INIT;
    @ assignable f.footprint;
    @ ensures \invariant_for(f);
    @ ensures f.state == FileReader.STATE_CLOSED;
    @ ensures !(\exists FileReader f; \fresh(f));
    @*/
  private static void use(FileReader f) {
    f.open();
    /*@
      @ loop_invariant \invariant_for(f) && f.state == FileReader.STATE_OPENED;
      @ loop_invariant !(\exists FileReader f; \fresh(f));
      @ assignable f.footprint;
      @ decreases f.remaining;
      @*/
    while (!f.eof()) {
      f.read();
    }
    f.close();
  }
}

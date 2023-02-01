public class GhostCode {
  /*@
    given int x;
    given int y;
    yields int res;
    ensures res == x + y;
  @*/
  void sum() {
    //@ ghost res = x + y;
  }

  void main() {
    //@ ghost int result;
    sum() /*@ with {x=3; y=2;} then {result=res;} @*/;
  }
}

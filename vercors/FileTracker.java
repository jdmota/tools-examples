public class FileTracker {
  //@ ghost private int active;

  //@ ensures PointsTo(active, 1, 0);
  public FileTracker() {
    //@ ghost active = 0;
  }
  
  //@ context Perm(active, 1);
  //@ ensures active == \old(active) + 1;
  public void inc() {
    //@ ghost active++;
  }

  //@ context Perm(active, 1);
  //@ ensures active == \old(active) - 1;
  public void dec() {
    //@ ghost active--;
  }
}

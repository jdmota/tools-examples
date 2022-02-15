/*@
predicate tracker(list<FileReader> readers) = true;
@*/

public class FileReadersTracker {

  public FileReadersTracker()
    //@ requires true;
    //@ ensures tracker(nil);
  {
    //@ close tracker(nil);
  }

  public FileReader newFileReader(String filename)
    //@ requires tracker(?readers);
    //@ ensures tracker(append(readers, cons(result, nil))) &*& filereader(result, FileReader.STATE_INIT, _) &*& result != null;
  {
    FileReader f = new FileReader(filename);
    //@ close tracker(append(readers, cons(f, nil)));
    return f;
  }

  public void dropFileReader(FileReader reader)
    //@ requires tracker(?readers) &*& filereader(reader, FileReader.STATE_CLOSED, _) &*& reader != null;
    //@ ensures tracker(remove(reader, readers));
  {
    //@ close tracker(remove(reader, readers));
  }

}
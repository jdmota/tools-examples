/*@
predicate tracker_list(list<FileReader> readers) = true;
@*/

public class FileReadersTracker {

  public FileReadersTracker()
    //@ requires true;
    //@ ensures tracker_list(nil);
  {
    //@ close tracker_list(nil);
  }

  public FileReader newFileReader(String filename)
    //@ requires tracker_list(?readers);
    //@ ensures tracker_list(append(readers, cons(result, nil))) &*& filereader(result, FileReader.STATE_INIT, _) &*& result != null;
  {
    FileReader f = new FileReader(filename);
    //@ close tracker_list(append(readers, cons(f, nil)));
    return f;
  }

  public void dropFileReader(FileReader reader)
    //@ requires tracker_list(?readers) &*& filereader(reader, FileReader.STATE_CLOSED, _) &*& reader != null;
    //@ ensures tracker_list(remove(reader, readers));
  {
    //@ close tracker_list(remove(reader, readers));
  }

}
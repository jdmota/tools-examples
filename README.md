# On using object-oriented tools to check object usage

## File Reader protocol

![File Reader Protocol](./file_reader_protocol.png)

Image generated with the [Typestate Editor](https://typestate-editor.github.io/).

Corresponding Mungo protocol:

```java
typestate FileProtocol {
  Init = {
    void open(): Open
  }
  Open = {
    boolean eof(): <true: Close, false: Read>
  }
  Read = {
    byte read(): Open
  }
  Close = {
    void close(): end
  }
}
```

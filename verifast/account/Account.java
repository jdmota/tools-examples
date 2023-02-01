//@ predicate account(Account a; int b) = a.balance |-> b &*& b >= 0;

class Account {
  int balance;

  void deposit(int value)
    //@ requires account(this, ?b) &*& 0 < value;
    //@ ensures account(this, b + value);
  {
    balance += value;
  }

  int getBalance()
    //@ requires [?f]account(this, _);
    //@ ensures [f]account(this, result);
  {
    return balance;
  }
}

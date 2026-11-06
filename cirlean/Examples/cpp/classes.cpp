// Classes: member functions, constructors, modular verification of callers
// against the specifications of the methods they call.
class Account {
  int balance_;

public:
  explicit Account(int b) : balance_(b) {}
  int balance() const { return balance_; }
  void deposit(int amt) { balance_ += amt; }
  bool withdraw(int amt) {
    if (amt < 0 || amt > balance_)
      return false;
    balance_ -= amt;
    return true;
  }
};

// Moves `amt` from `a` to `b` if `a` can afford it.
int transfer(Account &a, Account &b, int amt) {
  if (!a.withdraw(amt))
    return 0;
  b.deposit(amt);
  return 1;
}

// A local object: constructor, two calls, a query.
int open_and_use(int x) {
  Account acc(100);
  acc.deposit(x);
  acc.withdraw(30);
  return acc.balance();
}

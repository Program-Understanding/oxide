#include <iostream>

class Number
{
public:
    virtual int getNum() const { return 0;};
};

class One : public Number
{
public:
    virtual int getNum() const { return 1; }
};

class Two : public Number
{
public:
    virtual int getNum() const { return 2; }
};

int getNumber(Number *n)
{
  return n->getNum();
}

int main()
{
  One o;
  Two t;
  int i;

  i = getNumber(&o);
  i = getNumber(&t);
  return i;
}

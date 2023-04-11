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

class Three : public Number
{
public:
    virtual int getNum() const { return 3; }
};

class Four : public Number
{
public:
    virtual int getNum() const { return 1; }
};

int getNumber(Number *n)
{
  return n->getNum();
}

int main()
{
  One o;
  Two t;
  Three u;
  Four p;

  int i;

  i = getNumber(&o);
  i = getNumber(&t);
  i = getNumber(&u);
  i = getNumber(&p);
  return i;
}

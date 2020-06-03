#include "assert.h"
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void main()
{
  int w=1, z=0, x=0, y=0;
  while(unknown1()){
    while(x <= LARGE_INT && y <= LARGE_INT && unknown2()){
      if(w%2 == 1) 
        x++;
      if(z%2==0)
        y++;
    }
    while(w <= LARGE_INT && unknown4())
    {
      z=x+y;
      w=z+1;
    }
  }
  static_assert(x==y);
}

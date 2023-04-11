#include <stdio.h>
#include <stdlib.h>

int main()
{
   int c = 2;

   switch(c){
       case 1:c=c+1;break;
       case 2:c=c+2;break;
       case 3:c=c+3;break;
       case 4:c=c+4;break;
       case 5:c=c+5;break;
   }  
   return c;
}
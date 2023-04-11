int add (int a, int b)
    {return a+b;}
int main()
{
   int c = add(1,3); 

   switch(c){
       case 1:c=c+1;break;
       case 2:c=c+2;break;
       case 3:c=c+3;break;
       case 4:c=c+4;break;
       case 5:c=c+5;break;
       case 6:c=c+6;break;
       case 7:c=c+7;break;
   }  
   return c;
}
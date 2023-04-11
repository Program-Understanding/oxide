#include <stdio.h>
int main(){
    int x, y, z;
    x = 5;
here:
    y = 7;
    z = 10;
    if(y > 4)
        goto here;
    printf(z);
    return 5;
}
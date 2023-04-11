// Linear Obfuscation to combat Symbolic Execution
// Zhi Wang, Jiang Ming, Chunfu Jia, Debin Gao

#include<stdio.h>

int deadcode(){
    return 5;
}

int main(){
    int x;
    scanf("%d", &x);
    int y = 600 + x;
    int z = 0;
    while (y > 0){
        if(y % 2 == 0){
            y = y/2;
        }
        else if (y%2 == 1){
            y = 3*y-1;
        }
        if(x - y > 28 && x + y < 32){
            z = deadcode();
            break;
        }
    }
    return z;
}
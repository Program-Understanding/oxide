#include <stdlib.h>

void no_return(){
    exit(0);
}

int dead_code(){
    int x = 5;
    int y = 6;
    int z = 7;
    return x+y+z;
}
int main(){
    int a = 6;
    int b = 5;
    int c = 4;
    no_return();
    dead_code();
}
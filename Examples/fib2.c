#include<stdio.h>

int fib(int n) {
  int acc = 1;
  int i = n;
  while (i >= 2) {
    acc = fib(i-1) + acc;
    i = i - 2;
  }
  return acc;
}

int main() {
   printf("%i", fib(38));
}

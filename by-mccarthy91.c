#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

int mccarthy91 (int n) {
  int c;
  int ret = n;
  for (c = 1; c != 0; ) {
    if (ret > 100) {
      ret = ret - 10;
      c--;
    } else {
      ret = ret + 11;
      c++;
    }
  }
  return ret;
}  

int main (void) {
  int m;
  srand ((int) time (NULL));
  for (m = 0; m < 1000; m++) {
    int n = rand ();
    int result = mccarthy91 (n);
    if (!((n <= 100 && result == 91) ||
          (n  > 100 && result == n - 10))) {
      printf ("mccarthy91 (%d) = %d\n", n, result);
      _Exit (-1);
    }
  }
  printf ("pass 1000 random tests\n");
  return 0;
}

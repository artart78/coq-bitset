#include <sys/time.h>
#include <stdio.h>

/***/
int
timeval_subtract (result, x, y)
     struct timeval *result, *x, *y;
{
  /* Perform the carry for the later subtraction by updating y. */
  if (x->tv_usec < y->tv_usec) {
    int nsec = (y->tv_usec - x->tv_usec) / 1000000 + 1;
    y->tv_usec -= 1000000 * nsec;
    y->tv_sec += nsec;
  }
  if (x->tv_usec - y->tv_usec > 1000000) {
    int nsec = (x->tv_usec - y->tv_usec) / 1000000;
    y->tv_usec += 1000000 * nsec;
    y->tv_sec -= nsec;
  }

  /* Compute the time remaining to wait.
     tv_usec is certainly positive. */
  result->tv_sec = x->tv_sec - y->tv_sec;
  result->tv_usec = x->tv_usec - y->tv_usec;

  /* Return 1 if result is negative. */
  return x->tv_sec < y->tv_sec;
}
/***/

int t(int a,int b,int c){int d=0,e=a&~b&~c,f=1;if(a)for(f=0;d=(e-=d)&-e;f+=t(a-d,(b+d)*2,(
c+d)/2));return f;}

int main(){
	struct timeval start, end, diff;
	int i;
	for (i = 0; i < 30; i++) {
		gettimeofday(&start, NULL);
		int res = t(~(~0<<i),0,0);
		gettimeofday(&end, NULL);
		timeval_subtract(&diff, &end, &start);
		printf("%d [%f]\n", res, diff.tv_sec + ((double)diff.tv_usec / (1000 * 1000)));
	}
	return 0;
}

// Segmented sieve: print every r in [1, X] such that r, r+1, ..., r+L-1 are all y-smooth.
// Usage: smoothruns y X L   (exact: divides out all prime powers p<=y in each segment)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define SEG (1<<22)
int main(int c,char**v){ int y=atoi(v[1]); uint64_t X=strtoull(v[2],0,10); int L=atoi(v[3]);
  int P[4000],np=0; for(int p=2;p<=y;p++){int ok=1; for(int d=2;d*d<=p;d++) if(p%d==0){ok=0;break;} if(ok)P[np++]=p;}
  uint64_t *rem=malloc(SEG*8); int run=0; uint64_t cnt=0;
  for(uint64_t lo=1; lo<=X+L; lo+=SEG){
    uint64_t hi=lo+SEG; if(hi>X+L+1) hi=X+L+1; size_t n=hi-lo;
    for(size_t i=0;i<n;i++) rem[i]=lo+i;
    for(int j=0;j<np;j++){ uint64_t p=P[j]; uint64_t s=((lo+p-1)/p)*p;
      for(uint64_t m=s;m<hi;m+=p){ uint64_t *r=&rem[m-lo]; do *r/=p; while(*r%p==0); } }
    for(size_t i=0;i<n;i++){ if(rem[i]==1){ run++; if(run>=L){ uint64_t r=lo+i-L+1; if(r<=X){printf("%llu\n",(unsigned long long)r); cnt++;} } } else run=0; }
  }
  fprintf(stderr,"y=%d X=%llu L=%d runs=%llu\n",y,(unsigned long long)X,L,(unsigned long long)cnt); return 0; }

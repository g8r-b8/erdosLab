#include <stdio.h>
#include <stdlib.h>
/* for n in [n0,n1]: steps until orbit success (a - n), cap K*n steps; print stats + failures */
int main(int c,char**v){ long long n0=atoll(v[1]),n1=atoll(v[2]),cap=atoll(v[3]); long long maxs=0,maxn=0,fails=0; double sum=0;
 for(long long n=n0;n<=n1;n++){ long long d=n-2,a=n+1; int mir=0; long long st=-1;
  for(long long k=0;k<cap;k++){ if(d==-1||(mir&&(d==1||d==-1))){st=a-n;break;}
    if(d==0){mir=1;d=a;} else if(d==1) d=2-a; else d= d>0? 2*d-a : 2*d+a; a++; }
  if(st<0){fails++; if(fails<20) printf("FAIL n=%lld (cap %lld)\n",n,cap);} else {sum+=st; if(st>maxs){maxs=st;maxn=n;}}
 } printf("n in [%lld,%lld]: fails=%lld max steps=%lld at n=%lld mean=%.1f\n",n0,n1,fails,maxs,maxn,sum/(n1-n0+1-fails)); }

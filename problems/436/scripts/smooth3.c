// List all r <= X such that r, r+1, ..., r+L-1 are all y-smooth.  Output one r per line.
// Usage: smooth3 y X L
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int P[2000], np; static uint64_t X; static uint64_t *a; static size_t na, cap;
static void push(uint64_t v){ if(na==cap){cap=cap?2*cap:1<<20; a=realloc(a,cap*8); if(!a){fprintf(stderr,"oom\n");exit(1);} } a[na++]=v; }
static void gen(int i, uint64_t v){ push(v); for(int j=i;j<np;j++){ if(v > X/P[j]) break; uint64_t w=v*P[j]; gen(j,w);} }
static int cmp(const void*x,const void*y){ uint64_t u=*(uint64_t*)x,v=*(uint64_t*)y; return u<v?-1:u>v; }
int main(int c,char**v){ int y=atoi(v[1]); X=strtoull(v[2],0,10); int L=atoi(v[3]);
  for(int p=2;p<=y;p++){int ok=1; for(int d=2;d*d<=p;d++) if(p%d==0){ok=0;break;} if(ok)P[np++]=p;}
  gen(0,1); qsort(a,na,8,cmp); fprintf(stderr,"y=%d X=%llu smooth=%zu\n",y,(unsigned long long)X,na);
  size_t cnt=0; for(size_t i=0;i+L-1<na;i++){ if(a[i+L-1]-a[i]==(uint64_t)(L-1)){ printf("%llu\n",(unsigned long long)a[i]); cnt++; } }
  fprintf(stderr,"runs=%zu\n",cnt); return 0; }

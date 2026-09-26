#include <stdio.h>
#include <stdlib.h>
/* v_1=0, v_{a+1}=|a-2v_a|; print zeros a (and progress every 1e11) up to lim */
int main(int c,char**v){ unsigned long long lim=strtoull(v[1],0,10), a=1, x=0;
 printf("zero %llu\n",a); fflush(stdout);
 while(a<lim){ long long t=(long long)a-2*(long long)x; x=t<0?-t:t; a++;
  if(x==0){printf("zero %llu\n",a);fflush(stdout);}
  if(a%100000000000ULL==0){printf("reached %llu\n",a);fflush(stdout);} }
 printf("done %llu\n",lim); }

// Erdos #885 search: N1 in [lo,hi], columns = D(N1)\{0}; other rows N=b(b+d), b<=B.
// Report k=4 (4 rows sharing >=4 cols) counts and any k=5 (5 rows sharing >=5 cols).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef unsigned __int128 u128;
typedef struct {uint64_t key; u128 m;} E;
static int pc(u128 x){return __builtin_popcountll((uint64_t)x)+__builtin_popcountll((uint64_t)(x>>64));}
int main(int argc,char**argv){
  uint64_t lo=atoll(argv[1]),hi=atoll(argv[2]); uint64_t B=atoll(argv[3]); int mind=atoi(argv[4]);
  long k4=0,k5=0,tried=0;
  #pragma omp parallel reduction(+:k4,k5,tried)
  {
    int HB=23; size_t HS=1ul<<HB; E*H=calloc(HS,sizeof(E)); uint64_t*touch=malloc(sizeof(uint64_t)*(HS/2));
    uint64_t *cN=malloc(8*200000); u128*cM=malloc(16*200000);
    #pragma omp for schedule(dynamic,64)
    for(uint64_t N1=lo;N1<=hi;N1++){
      uint64_t d[128]; int nd=0;
      for(uint64_t a=1;a*a<N1 && nd<128;a++) if(N1%a==0){d[nd++]=N1/a-a;}
      if(nd<mind) continue;
      tried++;
      size_t nt=0;
      for(int j=0;j<nd;j++){
        for(uint64_t b=1;b<=B;b++){
          uint64_t N=b*(b+d[j]); if(N==N1) continue;
          size_t h=(N*0x9E3779B97F4A7C15ull)>>(64-HB);
          while(H[h].key && H[h].key!=N) h=(h+1)&(HS-1);
          if(!H[h].key){H[h].key=N;H[h].m=0; if(nt<HS/2) touch[nt++]=h;}
          H[h].m|=((u128)1)<<j;
        }
      }
      int nc=0;
      for(size_t t=0;t<nt;t++){E*e=&H[touch[t]]; if(pc(e->m)>=4 && nc<200000){cN[nc]=e->key;cM[nc]=e->m;nc++;} e->key=0;}
      // search triples (k=4: N1 + 3 others with >=4 common) and quadruples (k=5)
      for(int a=0;a<nc;a++) for(int b2=a+1;b2<nc;b2++){
        u128 m2=cM[a]&cM[b2]; if(pc(m2)<4) continue;
        for(int c=b2+1;c<nc;c++){
          u128 m3=m2&cM[c]; int p3=pc(m3); if(p3<4) continue;
          k4++;
          if(p3<5) continue;
          for(int e=c+1;e<nc;e++){
            u128 m4=m3&cM[e]; if(pc(m4)>=5){ k5++;
              #pragma omp critical
              { printf("K5 %llu %llu %llu %llu %llu cols:",(unsigned long long)N1,(unsigned long long)cN[a],(unsigned long long)cN[b2],(unsigned long long)cN[c],(unsigned long long)cN[e]);
                for(int j=0;j<nd;j++) if((m4>>j)&1) printf(" %llu",(unsigned long long)d[j]); printf("\n"); fflush(stdout);}
            }
          }
        }
      }
    }
  }
  fprintf(stderr,"range %llu-%llu B=%llu tried=%ld k4-configs=%ld k5=%ld\n",(unsigned long long)lo,(unsigned long long)hi,(unsigned long long)B,tried,k4,k5);
}

**Disproof of the "almost all N" version (and the full version, via Romanov): $f(N)\neq o(N)$**

*Disclosure: this argument was found and formalised with AI assistance (Claude). I have checked the argument myself; a Lean 4 / Mathlib formalisation of the main result is linked below.*

**Claim.** For every $K\geq 1$ and every $X$,
$$\#\{N<X : N\in D_n \text{ for some } n\leq N/K\}\leq \frac{S X}{K^2},\qquad S=\zeta(2)\sum_{b\geq 1}\frac{H_b}{b^2}=2\zeta(2)\zeta(3)\approx 3.955.$$
In particular $f(N)>N/3$ for more than $56\%$ of all $N<X$, for every $X$. So the answer to "perhaps just for almost all $N$?" is no: "$f(N)\leq \epsilon N$ for almost all $N$" fails for every $\epsilon<1/2$.

**Proof.** Suppose $N\in D_n$ and $Kn\leq N$. Then $N$ is the prefix sum up to some divisor $d>1$ of $n$. Write $d=n/e$ with $e\mid n$. Substituting $d'=n/e'$,
$$N\leq \sum_{d'\mid n,\ d'\leq d} d' = n\sum_{e'\mid n,\ e'\geq e}\frac{1}{e'} =: n\,T_e(n),$$
so $T_e(n)\geq K$. Also $n\leq X/K$ when $N<X$. Since $(n,e)\mapsto N$ maps onto the set being counted, Markov's inequality gives
$$\#\{\cdots\}\leq \sum_{n\leq X/K}\#\{e\mid n: T_e(n)\geq K\}\leq \frac1K\sum_{n\leq X/K}\sum_{e\mid n}T_e(n).$$
Swapping the order of summation,
$$\sum_{n\leq Y}\sum_{e\mid n}T_e(n)=\sum_{e\leq e'}\frac{1}{e'}\#\{n\leq Y:\mathrm{lcm}(e,e')\mid n\}\leq Y\sum_{e'}\frac{1}{e'^2}\sum_{e\leq e'}\frac{(e,e')}{e}.$$
Since $(e,e')\leq \sum_{g\mid e,\ g\mid e'} g$, the inner sum is at most $\sum_{g\mid e'}H_{e'/g}$. Writing $e'=gb$, the whole expression is at most $Y\sum_{g,b}\frac{H_b}{g^2b^2}=SY$. Therefore $\#\{\cdots\}\leq \frac1K\cdot S\cdot\frac XK$. $\blacksquare$

**The full question ($f(N)=o(N)$ for all $N$ where $f$ is defined).** If this held, then for every $K$ all large $N$ in $R=\bigcup_n D_n$ would be in the set counted above, so $R$ would have density $0$. But $R$ has positive lower density. If $p>2^k$ is prime, the divisors of $2^kp$ begin $2,4,\ldots,2^k,p$, so $p+2^{k+1}-2\in D_{2^kp}$. Hence $R\supseteq\{m-2: m=p+2^j,\ p>2^{j-1}\}$. The representations with $p\leq 2^{j-1}$ reach only $\ll X/\log X$ integers below $X$, so by Romanov's theorem (Math. Ann. 109 (1934); density of $\{p+2^j\}$ is $>0.1076$ by Elsholtz–Schlage-Puchta 2018) $R$ has lower density $>0.1$. Taking $K=7$ (so $S/K^2<0.081$) gives a positive proportion of $N\in R$ with $f(N)>N/7$. So $f(N)\neq o(N)$ in the literal sense too. Numerically $\{p+2^{k+1}-2: p>2^k\}$ has density $\approx 0.455$ up to $10^7$. Numerically $R$ has density close to $1$: $99.985\%$ of $N<20000$ lie in some $D_n$ with $n\leq 10^6$.

**Numerics** (consistent with Vjeko_Kovac's data above). At $X=2\cdot 10^5$, the fraction of $N<X$ with $N\in D_n$ for some $n\leq N/K$ is $0.319$ for $K=1$, $0.046$ for $K=2$ and $0.004$ for $K=3$.

**Formalisation.** [LINK: repo / file `E468.lean`] proves in Lean 4 + Mathlib:
- `card_covered_le`: $\#\{N<X:\exists n,\ Kn\leq N,\ N\in D_n\}\leq SX/K^2$;
- `not_erdos468MinimalPreimageLittleO_of_romanov`: the literal version is false, assuming only that $R$ has positive upper density (the Romanov input, stated as an explicit hypothesis, not an axiom); `mem_D_two_pow_mul_prime` is also formalised;
- `not_erdos468AlmostAll`: there is no $f$ with $f(N)=o(N)$ that is the minimal preimage on a set of density $1$. This is the "almost all" statement as phrased in google-deepmind/formal-conjectures PR #4076.

`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`; no `sorry`.

Full write-up: [LINK: PDF].

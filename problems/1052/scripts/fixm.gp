\\ Fixed-m search: all odd n with sigma*(n)/n = T := 2^(m+1)/(2^m+1) and exactly r odd components.
\\ Components q (pairwise coprime odd prime powers) sorted increasingly; prod (1+1/q) = T.
\\ Necessary conditions used for pruning (each proved in README):
\\  (R) every odd prime dividing 2^m+1 or q+1 (q a chosen component) divides n;
\\  (B) sum_q v2(q+1) = m+1, each term >= 1; v2(p^a+1) = v2(p+1) if a odd, 1 if a even.
default(factor_proven, 1);
NODES = 0; SOLS = List(); M = 0; FREEIT = 0;

ppbase(q) = my(p); if(q < 3 || q % 2 == 0, return(0)); if(isprimepower(q, &p), p, 0);
oddprimes(x) = my(f = factor(x)[,1]); select(p -> p > 2, f~);

addc(st, q, p) = {
  my(prims = setunion(st[2], [p]), req = setminus(st[3], [p]));
  foreach(oddprimes(q + 1), s, if(!setsearch(prims, s), req = setunion(req, [s])));
  [concat(st[1], q), prims, req, st[4] * (1 + 1/q), st[5] + valuation(q + 1, 2)]
}

\\ st = [comps, prims, req, P, used2]; r = remaining components
rec(st, r) = {
  my(comps = st[1], prims = st[2], req = st[3], P = st[4], used2 = st[5]);
  my(T = (2^(M+1) / (2^M + 1)) / P, last = if(#comps, comps[#comps], 1), u = #req);
  my(B = M + 1 - used2, E = B - r);
  NODES++;
  if(T <= 1 || u > r || E < 0, return);
  if(r == 1,
    my(q = 1 / (T - 1)); if(denominator(q) != 1 || q <= last, return);
    my(p = ppbase(q)); if(!p || setsearch(prims, p), return);
    if(u == 1 && req[1] != p, return);
    my(st2 = addc(st, q, p));
    if(#st2[3] || st2[5] != M + 1, return);
    listput(SOLS, [2^M * prod(i = 1, #st2[1], st2[1][i]), st2[1]]); return);
  if(r == 2,
    my(a = numerator(T), b = denominator(T), c = a - b, xs = List());
    if(u >= 1,
      my(s = req[1], x = s);
      while(c * x - b <= a * b, if(x > last, listput(xs, x)); x *= s),
      foreach(divisors(a * b), d, if((d + b) % c == 0, my(x = (d + b) / c); if(x > last, listput(xs, x)))));
    foreach(xs, x,
      my(px = ppbase(x)); if(!px || setsearch(prims, px), next);
      my(Tp = T / (1 + 1/x)); if(Tp <= 1, next);
      my(y = 1 / (Tp - 1)); if(denominator(y) != 1 || y <= last || y == x, next);
      my(py = ppbase(y)); if(!py || py == px || setsearch(prims, py), next);
      if(u == 0 && x > y, next);
      my(st2 = if(x < y, addc(addc(st, x, px), y, py), addc(addc(st, y, py), x, px)));
      if(#st2[3] || st2[5] != M + 1, next);
      listput(SOLS, [2^M * prod(i = 1, #st2[1], st2[1][i]), st2[1]]));
    return);
  my(lo = max(last + 1, floor(1 / (T - 1)) + 1));
  \\ (i) next component is a power of a required prime
  foreach(req, s,
    my(q = s); while(q < lo, q *= s);
    while((1 + 1/q)^r > T,
      if(valuation(q + 1, 2) - 1 <= E, rec(addc(st, q, s), r - 1));
      q *= s));
  if(u == r, return);
  \\ (ii) next component is free (prime not required): it is the smallest of the r-u free ones, and each
  \\ required prime s contributes at most 1+1/smin(s), smin(s) = least power of s above last.
  my(Tf = T); foreach(req, s, my(q = s); while(q <= last, q *= s); Tf /= (1 + 1/q));
  if(Tf <= 1, Tf = 1);
  my(rf = r - u, hi = if(Tf > 1, floor(rf * Tf / (Tf - 1)) + 1, 0));
  forstep(q = lo + (1 - lo % 2), hi, 2,
    FREEIT++;
    if(E == 0 && q % 4 == 3, next);
    if((1 + 1/q)^r <= T, break);
    if(Tf > 1 && (1 + 1/q)^rf < Tf, break);
    if(valuation(q + 1, 2) - 1 > E, next);
    my(p = ppbase(q)); if(!p || setsearch(prims, p) || setsearch(req, p), next);
    rec(addc(st, q, p), r - 1));
}

runm(m) = {
  M = m; SOLS = List(); NODES = 0; FREEIT = 0;
  my(req0 = Set(oddprimes(2^m + 1)), t = getabstime());
  for(r = 1, m + 1, rec([[], [], req0, 1, 0], r));
  printf("m=%d nodes=%d freeit=%d ms=%d sols=%s\n", m, NODES, FREEIT, getabstime() - t, Vec(SOLS));
}

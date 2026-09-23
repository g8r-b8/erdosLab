# Erdős Problem 132

**Database status checked 2026-08-30:** OPEN in `teorth/erdosproblems` (`data/problems.yaml`, current main).

**Experiment classification:** useful reformulation / exact counting lemma.

## Problem

Given `n` points in the plane, must there be at least two distinct distances which occur at least once but on at most `n` unordered pairs of points? Must the number of such low-multiplicity distances tend to infinity with `n`?

The diameter is known to occur on at most `n` pairs, so one low-multiplicity distance always exists. The difficulty is forcing more.

## Exact counting bridge

Let:

- `D` be the number of distinct positive distances determined by the point set;
- `L` be the number of those distance values whose multiplicity is at most `n`;
- `mu(d)` be the number of unordered pairs at distance `d`.

There are exactly `C(n,2)` unordered pairs, so

`sum_d mu(d) = C(n,2)`.

Every low-multiplicity distance occurs at least once. Every distance which is not low-multiplicity occurs at least `n+1` times. Therefore

`C(n,2) >= L + (D-L)(n+1)`.

Rearranging gives the exact general lower bound

`L >= (D(n+1) - C(n,2))/n`.

Since `L` is an integer, one may take the ceiling of the right-hand side.

### Immediate consequence

If `D > n/2`, then

`D(n+1) > (n/2)(n+1) = C(n,2) + n`,

and hence `L > 1`. Therefore `L >= 2`.

So:

**Any counterexample to the first question must determine at most `n/2` distinct distances.**

More generally, if

`D >= n/2 + g(n)`,

then the displayed inequality forces roughly `g(n)` additional low-multiplicity distance classes (up to the parity/rounding term). Thus any theorem giving a distinct-distance count exceeding `n/2` by an unbounded amount would automatically imply that the number of distance classes of multiplicity at most `n` tends to infinity.

## Prose version

Split the distance values into two kinds: cheap distances, used at most `n` times, and expensive distances, used at least `n+1` times. There are only `n choose 2` pairs available in total. If there are more than `n/2` different distance values, then trying to make all but one of them expensive already spends more pairs than exist. A second cheap distance is forced.

The open geometry therefore lives entirely in the regime where the configuration has comparatively few distinct distance values, or where one must exploit more structure than this global pair budget sees.

## Status / novelty note

This is an elementary reduction and no novelty claim is made. It isolates an exact numerical threshold linking the distinct-distances problem to Erdős #132. The current problem page records stronger geometric results in convex and related settings; this note is only the counting bridge.

Sources:
- https://www.erdosproblems.com/132
- Clemen, Dumitrescu, Liu (2025), arXiv:2505.04283, as linked on the problem page
- current status record: https://github.com/teorth/erdosproblems/blob/main/data/problems.yaml

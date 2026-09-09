# Bounded quantized-slice algebraization interface

Audience: a mathematical referee or a Lean maintainer checking the passage
from a formal quantum chart to an identity in the original algebra. The point
of this note is to state the finite lifting theorem that a quantum slice
argument must actually provide.

## The finite certificate

Let (U) be the original filtered ring, (A) a commutative coefficient ring,
and (S) the algebraic chart used by the differential/Ore descent interface.
Write

\[
  c(a,n,b)=\iota(a^n b)\in U,
  \qquad \iota: A\longrightarrow U,
  \qquad j:U\longrightarrow S.
\]

Let (Q) be a ring containing the formal or microlocal slice chart and let

\[
  e:S\longrightarrow Q
\]

be its chart map. Assume that both (j) and (e) are injective. For a fixed
nonzero (d\in U), a source (F\in U), and a finite list (T), require the
following data for every (t\in T):

\[
  (a_t,n_t)\text{ belongs to the prescribed finite coefficient cover},
  \qquad r_t,s_t\in U,
\]

and formal coefficients (q_{1,t},q_{2,t}\in Q) satisfying

\[
\begin{aligned}
 e(j(c(a_t,n_t,b_t)))
   &=e(j(d))q_{1,t}
     +\bigl(e(j(F))e(j(d))\bigr)q_{2,t},\\
 q_{1,t}&=e(j(r_t)),\
 q_{2,t}&=e(j(s_t)).
\end{aligned}
\]

The lifts must be bounded before any completion precision is chosen: there is
an integer (N) such that

\[
  \deg(r_t),\deg(s_t)\leq N
  \quad\text{for every }t\in T.
\]

Finally require the finite formal unit identity

\[
  \sum_{t\in T}e(j(c(a_t,n_t,b_t)))=1.
\]

The source (F), the list (T), and the bound (N) may depend on (d).
Nothing in this interface asks for one source independent of (d).

## Reflection theorem

Under these hypotheses, injectivity of (e) reflects the first displayed
identity to (S), and injectivity of (j) then gives, for each (t),

\[
  c(a_t,n_t,b_t)=d r_t+(F d)s_t
\]

in (U), with the factors in this order. The finite formal unit identity is
reflected in the same way, so the resulting list is a
`FiniteCoverClearance` for (d) and (F). The common bound is the maximum of
the finitely many (N_t), and monotonicity of the filtration preserves the
two cofactor bounds at that maximum.

Consequently, if such a finite certificate is supplied for every nonzero
(d\), it gives a `GlobalClearanceBridge`. The existing differential/Ore
consumer then returns

\[
  1=dR+(Fd)S
\]

in the original (U), and hence `OriginalSameDivisor U`. The Lean statements
are `ChartData.to_original_clearance`,
`ChartData.common_bound`, and `ChartData.GlobalBridge.consume` in
`SymplecticStafford/Source/QuantizedSliceAlgebraization.lean`.

## Proof and boundary

The proof only uses homomorphism laws, list induction, filtration monotonicity,
and the two injectivity hypotheses. It does not use a completion topology or
an unjustified specialization (h=1). In particular, the formal coefficients
are useful only after each one has a finite, bounded lift into the specified
algebraic chart.

This theorem does not assert that a formal Darboux--Weinstein decomposition
supplies those lifts. It does not turn torus-finiteness into membership in an
algebraic chart, replace a principal symbol by a power Ore set, or identify a
completed tensor factor with (S). It also does not provide the finite list,
the common bound, or the source (F). Supplying those data for the general
higher-dimensional quantization remains the unresolved producer in M01--M11.

The rational identity-chart oracle in
`tests/QuantizedSliceAlgebraizationOracle.lean` checks the theorem under
`--trust=0`. It is a concrete consumer check, not evidence that the general
quantum algebraization data exist.

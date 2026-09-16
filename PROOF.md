# Proof

Let $x_1\lt\cdots\lt x_n$ be interpolation nodes in $[-1,1]$, let $\ell_k$ be
their Lagrange fundamental polynomials, and put

```math
\lambda(x)=\sum_{k=1}^n |\ell_k(x)|.
```

Write $\Lambda_I$ for the maximum of $\lambda$ on an interval $I$. We prove
that for every fixed $-1\le a\lt b\le1$ and every $\varepsilon>0$, uniformly in
the nodes and for all sufficiently large $n$,

```math
\Lambda_{[a,b]}>
\left(\frac2\pi-\varepsilon\right)\log n. \qquad\text{(1)}
```

The formal proof first sorts an arbitrary injective enumeration. Lagrange
fundamentals and the Lebesgue function are invariant under this permutation,
so it is enough to work with strictly increasing nodes.

## 1. The sharp full-interval estimate

For $d=n-1$, define the clipped arcsine scale

```math
s_d(x)=\max\left\{\sqrt{1-x^2},
 \frac{3}{(d+1)(2d+1)}\right\}.
```

The proof introduces the unordered pair energy

```math
E_d(x_1,\ldots,x_n)
 =\sum_{j\lt k}\frac{\sqrt{s_d(x_j)s_d(x_k)}}{x_k-x_j}. \qquad\text{(2)}
```

Two estimates determine its size.

### Lower bound for the energy

Partition each half of $[-1,1]$ into geometric bins in the arcsine
coordinate. The ratio between successive scales is a fixed $q>1$, and the
number $B$ of reflected bins is $O_q(\log n)$. In a bin of Euclidean length
$h$, lower arcsine scale $s$, and containing $m$ nodes, the fixed-step overlap
identity and Cauchy--Schwarz give

```math
\sum_{r\le m/L}\ \sum_i
 \frac{s}{x_{i+r}-x_i}
 \ge \frac{s}{h}(m-m/L)^2 H_{m/L}. \qquad\text{(3)}
```

Here $L>1$ is fixed and $H_r$ is the $r$th harmonic number. Declare a bin
dense when it contains at least

```math
T=\left\lfloor\frac{n}{BR}\right\rfloor
```

nodes, with fixed $R\ge1$. Sparse bins discard at most $BT\le n/R$ nodes.
Applying weighted Cauchy--Schwarz across the dense bins and using the exact
reflected arcsine budget

```math
\sum_{\text{bins}}\frac{h}{s}\le q\pi
```

yields

```math
E_d\ge
 \frac{(1-1/R)^2(1-1/L)^2(1-\eta)}{q\pi}
 n^2\log n \qquad\text{(4)}
```

for every fixed $q,R,L,\eta$ as above and all sufficiently large $n$.
The only asymptotic input here is $B=O_q(\log n)$, which implies
$H_{T/L}\ge(1-\eta)\log n$ eventually.

### Upper bound for the energy

For each node $x_j$, form the signed derivative-row polynomial

```math
P_j=\sum_{k\ne j}\mathrm{sgn}(\ell_k'(x_j))\ell_k.
```

Its values are bounded by the full Lebesgue constant
$\Lambda_{[-1,1]}$, while $P_j'(x_j)$ is the sum of the absolute derivative
entries in row $j$. An exact finite Riesz interpolation formula proves the
sharp weighted Bernstein estimate in the interior. A bounded Chebyshev
expansion and the estimates $|U_k|\le k+1$ and $|T_k'|\le k^2$ supply the
positive endpoint floor in $s_d$. Together they give the clipped pointwise
bound needed for every row polynomial.

Pairing the two directed derivative entries for each unordered pair then
gives

```math
2E_d\le n(n-1)\Lambda_{[-1,1]}. \qquad\text{(5)}
```

Combining (4) and (5), and choosing $q\downarrow1$, $R,L\to\infty$, and
$\eta\downarrow0$, proves

```math
\Lambda_{[-1,1]}>
\left(\frac2\pi-\varepsilon\right)\log n \qquad\text{(6)}
```

uniformly over all node arrays.

## 2. Equioscillating arrays and coordinatewise comparison

Fix the two endpoint nodes $A\lt B$ and allow $d$ interior nodes to vary. For
each of the $d+1$ consecutive nodal gaps, let $h_i$ be the maximum of the
Lebesgue function on that gap. The formalization reconstructs the theorem of
de Boor and Pinkus needed below:

1. there is a unique endpoint-fixed array for which all $h_i$ are equal; and
2. if two endpoint-fixed arrays $s,t$ satisfy $h_i(s)\le h_i(t)$ for every
   gap, then $s=t$.

The proof is internal to the Lean development. It establishes the gap
critical-point and interlacing theory, coherent signs of the maximal Jacobian
minors, boundary escape, properness, local inversion, global inversion, and
the two oriented continuation arguments that yield coordinatewise rigidity.

For the equioscillating array on $[-1,1]$, the closed nodal gaps cover the
whole interval, so its common height is exactly its full Lebesgue constant.
Affine invariance transports this statement to the normalized interval
$[0,1]$. Thus (6) is also a sharp lower bound for the common height of every
sufficiently large equioscillating pattern.

## 3. Localizing the height to an arbitrary consecutive block

Take any consecutive block of $m\ge2$ nodes in a larger ordered array.
Replace that block by a small affine copy of the equioscillating $m$-node
pattern, leaving all exterior nodes fixed and preserving the two extreme
nodes of the full array.

As the copy collapses:

- every internal block-gap height converges to the common pattern height;
- every exterior or bridge-gap height tends to infinity; and
- the modified array remains strictly ordered for a sufficiently small
  positive scale.

If every original internal block gap were strictly below the pattern height,
one sufficiently collapsed comparison array would have every gap height
strictly larger than the corresponding original height. Coordinatewise
rigidity would force the two arrays to be equal, contradicting the genuine
movement of the block. Therefore some original internal block gap has height
at least the equioscillating $m$-node height. This argument treats full,
left-endpoint, right-endpoint, and interior blocks separately.

## 4. Sparse damping versus a dense block

Choose fixed nested intervals

```math
J_0\subset\mathrm{int}(J_1)\subset[a,b].
```

A fixed-interval interpolation estimate gives a constant $C_0>1$ such that
every polynomial $p$ satisfies

```math
\|p\|_{[-1,1]}\le C_0^{\deg p}\|p\|_{J_0}. \qquad\text{(7)}
```

Let $m$ be the number of interpolation nodes in $J_1$. If $m$ is small, form
the polynomial $Q$ vanishing at those nodes, choose $x_*\in J_0$ where
$|Q|$ is maximal, and multiply $Q/Q(x_*)$ by a high power of the quadratic
damping factor

```math
D(x)=1-\frac18(x-x_*)^2.
```

The resulting polynomial has degree below $n$, equals one at $x_*$, vanishes
at all nodes in $J_1$, and is exponentially small at every remaining node.
Lagrange interpolation therefore forces $\lambda(x_*)$ to be exponentially
large, which is stronger than (1).

Otherwise $m$ is a fixed positive proportion of $n$. Because the nodes are
ordered and $J_1$ is an interval, these $m$ indices form a literal consecutive
block and every internal block gap lies in $[a,b]$. Apply the block theorem
from the previous section. The sharp equioscillating-height bound gives a
point $t\in[a,b]$ with

```math
\lambda(t)>
\left(\frac2\pi-\frac\varepsilon2\right)\log m.
```

The density relation gives $m\ge c n$ for a fixed $c>0$. Hence
$\log m\ge\log n-O(1)$, and the fixed additive loss is absorbed by the spare
$\varepsilon\log n/2$ for all sufficiently large $n$. This proves (1) for
ordered nodes.

Finally, sorting an arbitrary injective enumeration preserves the Lebesgue
function pointwise. Transporting the ordered result back through that
permutation proves the stated theorem. $\square$

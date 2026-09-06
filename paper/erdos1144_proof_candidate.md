# Erdős problem 1144 — a complete proof candidate

**[Read or download the typeset PDF](erdos1144_proof_candidate.pdf)**

Original exposition: 5 September 2026. Presentation and status note updated
6 September 2026.

**Status.** This document is the informal proof candidate, retained with its
mathematical claims unchanged. The repository now contains a kernel-checked
Lean proof of the conclusion (T), completed on 6 September 2026:
[`Erdos.Problem1144.erdos1144`](../Erdos/Problem1144/Final.lean).
Its [endpoint axiom audit](../verification/axiom-audit.txt) reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; the
[independent GitHub build and audit passed](https://github.com/saasom/Erdos1144/actions/runs/34025001677).
The [completed proof guide](../notes/1144/complete_proof.md) describes the
formal argument. This exposition is not itself a formal proof, has not been
externally refereed, and has not been checked for line-by-line correspondence
with the Lean development. The formal verification claim applies to the Lean
endpoint, not to every intermediate assertion in this dated exposition.

## Statement and notation

Let $(\varepsilon_p)_p$ be independent fair signs. Define $f$ completely multiplicatively by $f(p)=\varepsilon_p$, and put $g(n)=\mu^2(n)f(n)$. Write

$$
S(x)=\sum_{n\le x}f(n),\quad M(x)=\sum_{n\le x}g(n),\quad
A(x)=S(x)/\sqrt x,\quad R(x)=\sum_{n\le x}g(n)/\sqrt n.
$$

On logarithmic time, let

$$
a(t)=A(e^t),\quad m(t)=e^{-t/2}M(e^t),\quad r(t)=R(e^t).
$$

Set $a(t)=m(t)=0$ for $t<0$.

The proposed conclusion is

$$
\mathbb P\!\left(\limsup_{N\to\infty}S(N)/\sqrt N=+\infty\right)=1.
\tag{T}
$$

All limits below can be taken along positive integral $T\to\infty$. Constants in estimates under a fixed finite-prime conditional law may depend on that law. The final positive crossing probability does not.

## 1. Inputs and elementary identities

Squarefree orthogonality and the decomposition $n=dr^2$ give

$$
A(x)=R(x)+E(x),\qquad
E(x)=-x^{-1/2}\sum_{d\le x}g(d)\{\sqrt{x/d}\},
\tag{1}
$$

$$
\mathbb E E(x)^2\le1,\qquad
\mathbb E A(e^t)^2\ll t+1.
\tag{2}
$$

We use [Atherfold's weighted upper bound, Theorem 1](https://arxiv.org/html/2501.11076v4): for any fixed $\gamma>3/4$, almost surely

$$
|r(t)|\le K_f(\log(t+2))^\gamma\quad(t\ge0)
\tag{3}
$$

for a finite random $K_f$.

The relevant Dirichlet series satisfy, almost surely on $\Re s>1/2$,

$$
F_c(s)=\sum_n f(n)n^{-s}
=\zeta(2s)F_g(s),\qquad
F_g(s)=\sum_n g(n)n^{-s}.
\tag{4}
$$

In particular $F_c(s)>0$ for real $s>1/2$.
These convergence statements do not require (T): the elementary dyadic maximal inequality for orthogonal sums gives
$M(x)\ll_f\sqrt x(\log(2x))^2$ almost surely, and summing $M(x/r^2)$ gives
$S(x)\ll_f\sqrt x(\log(2x))^3$. Partial summation and analytic continuation from $\Re s>1$ then justify (4) and

$$
\int_0^\infty a(t)e^{-zt}\,dt
=\frac{F_c(1/2+z)}{1/2+z},\qquad \Re z>0.
\tag{5}
$$

For positivity, apply the same maximal argument to the prime-supported sign sequence. It gives
$\sum_{p\le x}\varepsilon_p\ll_f\sqrt x(\log(2x))^2$, so
$\sum_p\varepsilon_p p^{-s}$ converges locally uniformly almost surely on $\Re s>1/2$. The prime-power terms of degree at least two converge absolutely there. Continuing the Euler product from $\Re s>1$ therefore gives

$$
F_c(s)=\exp\!\left\{\sum_p\varepsilon_p p^{-s}
+\sum_p\sum_{k\ge2}\frac{\varepsilon_p^k}{k p^{ks}}\right\}.
\tag{5a}
$$

The exponent is real for real $s>1/2$, proving the positivity used below.

We also use the uniform estimate

$$
|1/\zeta(v+it)|\ll\log(|t|+2)\quad(v\ge1).
\tag{6}
$$

For large $|t|$, this follows, for example, from [Leong, Corollary 4](https://arxiv.org/html/2405.04869v5); bounded heights follow from zero-freeness on $\Re s\ge1$, continuity of $1/\zeta$ at its zero at $s=1$, and absolute convergence when $v$ is large.

### The squarefree Gaussian input

We need the following consequence of [Harper, Propositions 1–2 and Normal Comparison Result 1](https://arxiv.org/html/2012.15809). Let $V\to\infty$, $Y=e^V$, and

$$
u_i=8V/7+2\pi i,\qquad 0\le i\le 2V/(21\pi).
$$

Conditional on the multiplicative signs, define the centered Gaussian field

$$
H_i=\sum_{Y<p\le e^{u_i}}N_p\frac{M(e^{u_i}/p)}{e^{u_i/2}}.
\tag{7}
$$

There are events of probability tending to one on which, **simultaneously for all retained subsets** of size $V^{1-o(1)}$, the conditional probability that their absolute maximum exceeds

$$
L_V=(\log V)^{1/4}\exp\{-2\sqrt{\log\log V}\}
\tag{8}
$$

tends to one.

Here is the quantitative justification for that consequence. Use Harper's parameter $w=\sqrt{\log\log V}$. His variance lower bound is $\gg e^{-2.2w}/\sqrt{\log V}$; his covariance result bounds each bad degree by $V^{0.7}$, at threshold $(\log V)^{-0.6}$. Greedy deletion therefore leaves $V^{0.3-o(1)}$ coordinates with normalized correlations tending to zero. Normal comparison proves (8). These regularity events concern small-prime signs and hold uniformly over the retained sets; the sets may depend on further multiplicative signs, but not on the Gaussian noises.

## 2. A prime Gaussian sum can be coupled to logarithmic white noise

We give the approximation needed for both complete and squarefree sums. Fix $1<\alpha<\beta$, and consider $O(T)$ deterministic points $t_i\in[\alpha T,\beta T]$. For $b=a$ or $b=m$, set

$$
P_i^{(b)}=\sum_{e^T<p\le e^{t_i}}N_p p^{-1/2}b(t_i-\log p),
\quad
B_i^{(b)}=\int_T^\infty b(t_i-v)\frac{dB(v)}{\sqrt v}.
\tag{9}
$$

There is a joint Gaussian coupling, conditional on the multiplicative signs, for which

$$
\max_i|P_i^{(b)}-B_i^{(b)}|=o_{\mathbb P}(1).
\tag{10}
$$

The error is uniform over these grids and remains $o(1)$ under any fixed finite-prime conditional law. The Gaussian noises are independent of all multiplicative signs.

### Proof of the approximation

First, for $0<h\le1$ and $L\ge1$,

$$
\int_{-h}^L\mathbb E|a(v+h)-a(v)|^2\,dv
\ll h(L+1)+h^2(L+1)^2.
\tag{11}
$$

The change in $e^{-v/2}$ contributes $O(h^2(L+1)^2)$, by (2). For the summation change, expand the expected square. A pair $n,m$ survives only if $nm$ is a square. Its integrated weight is at most $Ch/\max(n,m)$, and it occurs only if $|\log(n/m)|\le h$. Write $n=dA^2,m=dB^2$, with $d$ squarefree. The diagonal contributes $O(h(L+1))$. For $B>A$, the number of permissible $B$'s is $O(hA)$, and hence the off-diagonal contribution is at most

$$
Ch^2\sum_{A\le e^{(L+1)/2}}\frac1A
\sum_{d\le e^{L+1}/A^2}\frac1d
\ll h^2(L+1)^2.
$$

The jump at zero contributes $O(h)$. The squarefree version follows by the same argument, with only the diagonal surviving.

We also need a discrete envelope version of (11). For any grid of spacing $h$, enlarging each interval of summands to a log-window of width $Ch$, the sum of its expected normalized squared sums, multiplied by $h$, is

$$
O(h(L+1)+h^2(L+1)^2).
\tag{12}
$$

Indeed, each surviving square-correlated pair occurs in $O(1)$ such windows and has weight $O(h/\max(n,m))$. This is a comparison of **expected squares**, using nonnegative pair correlations; no pointwise comparison of signed sums is asserted.

Choose $\delta=e^{-T^\nu}$, where $0<\nu<1/2$. These restrictions ensure that $\delta$ is smaller than every inverse power of $T$ and larger than the classical prime-number-theorem relative error. Partition the log-prime interval into bins of length $\delta$. For a full bin $J\subset[T,\beta T]$, the classical estimate for $\vartheta$ and partial summation give, uniformly,

$$
\sum_{\log p\in J}\frac{\log p}{p}
=\delta(1+\epsilon_J),\qquad
\max_J|\epsilon_J|
\ll \delta^{-1}e^{-c\sqrt T}+\delta.
\tag{13}
$$

Write each prime coefficient as
$\sqrt{\log p/p}\,b(t_i-\log p)/\sqrt{\log p}$.
Replace its last factor by the bin-endpoint value. Equation (12), the upper bound in (13), and $v\asymp T$ show that the expected squared error per coordinate is

$$
O(\delta+\delta^2T).
$$

The variation of $v^{-1/2}$ contributes a smaller error.
The weighted Gaussian sums on disjoint bins are independent. Couple each with a Brownian increment by using the same standard normal. The variance replacement contributes at most

$$
O\!\left(T(\delta^{-1}e^{-c\sqrt T}+\delta)^2\right)
$$

per coordinate, since $\int_0^{(\beta-1)T+1}\mathbb E a(v)^2\,dv\ll T^2$.
Replacing the Brownian step integrand by the actual integrand uses (11) again. A final partial bin is covered by the same enlarged-window estimate, including the possible jump at zero.

Summing these errors over $O(T)$ coordinates gives $o(1)$, proving (10) by Markov's inequality. Conditioning on a fixed cylinder multiplies expectation bounds by at most the reciprocal of its probability. This proves the asserted conditional-law version.

## 3. Stationary squarefree Gaussian maxima

Fix $\sigma>0$, write $V=1/\sigma$, and define the stationary centered Gaussian field with covariance

$$
Q_g(s,t)=\frac1V\int_{\mathbb R}
m(s-v)m(t-v)e^{-\sigma(s+t-2v)}\,dv.
\tag{14}
$$

This is well-defined almost surely. Take a grid of spacing $2\pi$ and length

$$
D=V/W,\qquad W\to\infty,\qquad \log W=o(\log V).
\tag{15}
$$

Retain any fixed positive proportion of its points, with the selection measurable in the multiplicative signs.

By stationarity, translate the grid to the points $u_i=8V/7+2\pi i$ used in (7). Its retained size is $V^{1-o(1)}$. Let $C_H$ be the covariance of the white-noise counterpart of (7):

$$
(C_H)_{ij}=\int_V^\infty m(u_i-v)m(u_j-v)\frac{dv}{v}.
$$

Put $R_i=e^{-\sigma(u_i-V)}$. Restricting the integral in (14) to $v\ge V$ gives the positive-semidefinite inequality

$$
Q_g\succeq R C_H R,
\tag{16}
$$

because $e^{2\sigma(v-V)}/V\ge1/v$ there. The diagonal factors satisfy
$\min_iR_i\ge e^{-1/7-D/V}$, which stays bounded away from zero.

The approximation (10) and Harper's input show that the absolute maximum of the white-noise field on every such retained set exceeds a constant multiple of $L_V$, with probability tending to one. Anderson's inequality transfers this assertion through (16): for centered Gaussian vectors, adding a positive-semidefinite covariance component cannot increase the probability of a symmetric box. Thus the same lower bound holds for the field (14).

All assertions in this section remain valid under any fixed finite-prime conditional law. Harper's exceptional-event probabilities tend to zero and may be divided by the fixed cylinder probability. The approximation error is uniform over the whole grid, and hence over all its retained subsets.

## 4. Transfer from the stationary squarefree field to the complete field

Write $X=e^T$, $j=\log T$. Fix $\gamma>3/4$ as in (3), choose fixed $1<\alpha<\beta<4/3$, and set

$$
\begin{gathered}
c_0=\alpha-1,\qquad
W=\kappa\log j,\qquad
\kappa>\frac{\gamma+1/2}{c_0},\\
\sigma=W/T,\quad V=1/\sigma=T/W,\quad D=T/W^2.
\end{gathered}
\tag{17}
$$

The condition on $\kappa$ is derived from the tail estimate below. Let $t_i$ be any deterministic $2\pi$-spaced grid of width at most $D$ in $[\alpha T,\beta T]$, with $\asymp D$ points. Retain any fixed positive proportion.

Define the stationary complete covariance

$$
Q_c(s,t)=\frac1T\int_{\mathbb R}
a(s-v)a(t-v)e^{-\sigma(s+t-2v)}\,dv.
\tag{18}
$$

By Parseval and (4), its spectral density is

$$
\frac1{2\pi T}
\left|\frac{\zeta(1+2\sigma+2i\tau)F_g(1/2+\sigma+i\tau)}
{1/2+\sigma+i\tau}\right|^2.
\tag{19}
$$

The density of (14) is the same expression with $\zeta$ omitted and $T$ replaced by $V$.

Set $H=j^2$. The portion of the squarefree field (14) at $|\tau|>H$ has expected coordinate variance $O(1/H)$. Indeed, orthogonality gives

$$
\mathbb E|F_g(1/2+\sigma+i\tau)|^2
=\sum_n\frac{\mu^2(n)}{n^{1+2\sigma}}\ll1/\sigma=V.
$$

For $O(T)$ Gaussian coordinates the expected squared maximum of this high-frequency field is therefore

$$
O(\log(T+2)/H)=o(1).
\tag{20}
$$

This remains true under a fixed cylinder. Consequently the low-frequency squarefree field still has absolute maximum $\gg L_V$ with probability tending to one.

By (6), on $|\tau|\le H$ the complete density (19) dominates the low-frequency squarefree density by

$$
\frac{c}{W\log^2(H+2)}.
\tag{21}
$$

A second application of Anderson's inequality gives a diverging absolute maximum for (18), of size at least a constant multiple of

$$
\frac{L_V}{\sqrt W\log(H+2)}\longrightarrow\infty.
\tag{22}
$$

Here $\log V\sim j$, and $L_V=j^{1/4-o(1)}$, whereas the denominator is a power of $\log j$.

### The stationary extension has negligible error

Let $Q_{c,\mathrm{tr}}$ denote (18) restricted to $v\ge T$. The Gaussian field omitted by this restriction is independent of the retained white-noise field conditional on $f$, and its coordinate variances are at most

$$
\frac1T\int_{c_0T}^\infty a(u)^2e^{-2Wu/T}\,du.
\tag{23}
$$

From (1)–(3), this is at most

$$
C K_f^2\,\frac{e^{-2c_0W}}W j^{2\gamma}+V_E,\qquad
\mathbb E V_E\ll e^{-2c_0W}/W.
\tag{24}
$$

The elementary integral estimate here follows by substituting $u=c_0T+vT/W$.
Gaussian maximum estimates cost only $\log(T+2)$. First restrict to $K_f\le K$, and then let $K\to\infty$; (17) makes

$$
j^{2\gamma+1}e^{-2c_0W}/W\to0.
$$

The error term in (24) is handled by its expectation. Hence the maximum stationary-extension error is $o_{\mathbb P}(1)$, also under any fixed cylinder. The diverging maximum in (22) therefore holds for $Q_{c,\mathrm{tr}}$.

## 5. The actual complete fresh Gaussian and Rademacher fields

Let $t_0=\min_i t_i$, and let $C_{\mathrm{white}}$ be the covariance

$$
(C_{\mathrm{white}})_{ik}
=\int_T^\infty a(t_i-v)a(t_k-v)\frac{dv}{v}.
\tag{25}
$$

Set $\Delta=\operatorname{diag}(e^{-\sigma(t_i-t_0)})$. An exact pointwise comparison of the scalar integration weights gives

$$
\Delta^{-1}Q_{c,\mathrm{tr}}\Delta^{-1}
\preceq \beta e^{2\sigma D_{\mathrm{width}}}C_{\mathrm{white}},
\qquad D_{\mathrm{width}}=\max_i t_i-\min_i t_i\le D.
\tag{26}
$$

Indeed, the left-hand integrand has scalar weight
$e^{2\sigma(v-t_0)}/T$, while active $v$'s satisfy
$T\le v\le\beta T$ and $v\le t_0+D_{\mathrm{width}}$.
The scalar factor on the right stays bounded, since $\sigma D=1/W$; the diagonal factors also stay bounded above and below.
Thus Anderson's inequality and (22)–(24) give a diverging absolute maximum for (25). Approximation (10) transfers this to the Gaussian field

$$
Z_i=\frac1{e^{t_i/2}}\sum_{e^T<p\le e^{t_i}}N_pS(e^{t_i}/p).
\tag{27}
$$

For clarity about conditioning: (14) and (18) use unbounded inner times. Whenever conditioning on the old signs $p\le X$, complete them with an **auxiliary independent continuation**, independent of the Gaussian noises. It agrees with the actual old function. The fields (25) and (27) use only old values because $t_i-T<T$; they are unchanged by the continuation. All spectral and tail comparisons may be conditioned on the auxiliary full function and then averaged over its continuation. The actual fresh Rademacher signs are never included in this conditioning. Although the auxiliary continuation may change with $T$, its full law is always the same fixed-prefix law $Q$. Thus the truncation of $K_f$ in the tail argument uses a tight family with one fixed distribution, not a common pathwise constant across continuations.

Finally replace the $N_p$'s in (27) by the actual fresh signs:

$$
Y_i=\frac1{e^{t_i/2}}\sum_{e^T<p\le e^{t_i}}\varepsilon_pS(e^{t_i}/p).
\tag{28}
$$

Conditional on the old signs these are linear sums of independent signs. The multivariate normal approximation used by Harper applies also to the doubled coordinate set $(Y_i,-Y_i)$. For a fixed smoothing margin, its error tends to zero **deterministically** here: writing $m_T=O(T)$ for the grid size and using $|S(z)|\le z$, the two error terms are bounded by constants times

$$
m_T^2 e^{(\beta-3/2)T}
+m_T^3 e^{(3\beta/2-2)T}=o(1).
\tag{29}
$$

Both exponents are negative because $\beta<4/3$. The same bounds apply to any old-measurable retained subset.

We have therefore established the following robust crossing statement. For every fixed finite-prime conditional law $Q$, every deterministic narrow grid as above, every old-measurable retained subset $J_T$ of fixed positive density, and every fixed $K>0$,

$$
Q\!\left(\max_{i\in J_T}|Y_i|>K\right)\longrightarrow1.
\tag{30}
$$

Joint conditional symmetry gives

$$
\liminf_{T\to\infty}Q\!\left(\max_{i\in J_T}Y_i>K\right)\ge\frac12.
\tag{31}
$$

This last constant is independent of the finite initial assignment.

## 6. Contradiction to an almost surely finite upper envelope

Put

$$
C(f)=\sup_{t\ge0}a(t),\qquad E_M=\{C(f)\le M\}.
$$

The failure of (T) is $\{C(f)<\infty\}$: the function $a$ is bounded on compact intervals, and integer and real positive excursions are equivalent.

Suppose this failure event has positive probability. By conditional-probability convergence along finite prime prefixes, and then $E_M\uparrow\{C<\infty\}$, for any sufficiently small fixed $\delta>0$ there exist a finite-prime cylinder $C_0$, its conditional law $Q$, and finite $M\ge1$, such that

$$
Q(E_M)>1-\delta.
\tag{32}
$$

On $E_M$, (5) and positivity of the real Euler product imply

$$
0\le\int_0^\infty a(t)e^{-t/T}\,dt,
\qquad
\int_0^\infty a^-(t)e^{-t/T}\,dt\le MT.
\tag{33}
$$

Thus, for every $b>0$,

$$
\int_{\alpha T}^{\beta T}Q(a(t)<-b)\,dt
\le \delta(\beta-\alpha)T+e^\beta MT/b.
\tag{34}
$$

Let $\mathcal F_X=\sigma(\varepsilon_p:p\le X)$, $X=e^T$, and
$w_T(t)=\mathbb E[A(e^t)\mid\mathcal F_X]$.
For $t<2T$, complete multiplicativity gives the exact splitting

$$
a(t)=w_T(t)+Y_t
\tag{35}
$$

with the fresh linear field (28). Its conditional symmetry implies, under $Q$ once the fixed prefix lies below $X$,

$$
Q(w_T(t)<-b)\le2Q(a(t)<-b).
\tag{36}
$$

Partition almost all of $[\alpha T,\beta T]$ into blocks of length $2\pi m_T$, where $m_T=\lfloor D/(2\pi)\rfloor$, and average a $2\pi$-spaced grid over its shift in $[0,2\pi)$. Averaging jointly over blocks and shifts, (34)–(36) yield a **deterministic** block and shift with

$$
\mathbb E_Q\frac{\#\{i:w_T(t_i)<-b\}}{m_T}
\le2\delta+\frac{2e^\beta M}{b(\beta-\alpha)}+o(1).
\tag{37}
$$

The discarded interval has length $O(D)=o(T)$. Choosing the block by these probabilities uses no realized signs or future randomness. In particular there is no factor $T/D$ in (37).

Fix $0<\rho<1$. Markov's inequality shows that the good set

$$
G_T=\{i:w_T(t_i)\ge-b\}
$$

has at least $\rho m_T$ elements except on an event of probability at most

$$
\frac{2\delta+2e^\beta M/[b(\beta-\alpha)]}{1-\rho}+o(1).
\tag{38}
$$

Use $J_T=G_T$ when this size condition holds and the full grid otherwise. This selector is old-measurable and always has the required size.

Apply (31) with the fixed threshold $K=M+b$. On the good-size event, any resulting positive crossing gives $a(t_i)>M$, which is impossible on $E_M$. Equations (32) and (38) therefore imply

$$
\frac12\le
\delta+
\frac{2\delta+2e^\beta M/[b(\beta-\alpha)]}{1-\rho}.
\tag{39}
$$

Choose $\delta>0$ small enough that
$\delta+2\delta/(1-\rho)<1/2$, obtain $Q,M$ from (32), and then choose the fixed $b$ sufficiently large. This contradicts (39).

Hence $\mathbb P(C(f)<\infty)=0$. Since $a(t)$ is bounded on every compact interval, its positive limsup is infinite almost surely. If $S(x)/\sqrt x>K>0$, then for $N=\lfloor x\rfloor$,
$S(N)/\sqrt N\ge S(x)/\sqrt x>K$; the indices tend to infinity. This proves (T).

## Checks and scope

The essential new steps are the averaged negative-tail contradiction, the logarithmic prime-to-white-noise coupling for the complete model, and the two stationary covariance comparisons. No direct covariance domination between complete and squarefree unsmoothed partial sums is asserted. No square-kernel error estimate is applied at a selected random endpoint. The large-prime signs remain independent at every normal-approximation step.

Separate mathematical checks in this session examined the arithmetic approximation and analytic inputs, the Gaussian covariance comparisons and Harper invocation, and the finite-prefix probability argument. They requested the explicit positivity argument (5a), preservation of the constant in Harper's variance estimate, and the tightness explanation for changing auxiliary continuations; these have been incorporated. No remaining mathematical gap was identified in those checks. Those checks were internal mathematical review of the 5 September exposition, not external refereeing or a line-by-line formal verification. For the subsequently verified Lean endpoint, see the status note above.

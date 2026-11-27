/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# Challenge: Erdős Problem 1221, the case `r = 1`

This file is the human-auditable statement. It imports only Mathlib.

Place points `a 0, a 1, …` on the circle `ℝ/ℤ`. For the first `n` points, `maxSpan a n 1` and
`minSpan a n 1` are the longest and shortest of the `n` arcs between consecutive points.
`bigLambda 1` is the infimum, over sequences with pairwise distinct points, of
`limsup n · maxSpan`; `smallLambda 1` is the supremum of `liminf n · minSpan`; and `mu 1` is the
infimum of `limsup maxSpan / minSpan`. De Bruijn and Erdős [dBEr49, §§2–5] proved
`Λ₁ = 1/log 2`, `λ₁ = 1/log 4` and `μ₁ = 2`.

The definitions and the statement are copied verbatim from
`FormalConjectures/ErdosProblems/1221.lean` (`Erdos1221.erdos_1221.variants.r_one`) in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
at commit `ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8`, except that the repository's
`@[category …]` attribute is dropped.

*References:*
- [erdosproblems.com/1221](https://www.erdosproblems.com/1221)
- [dBEr49] de Bruijn, N. G. and Erdős, P., *Sequences of points on a circle*. Nederl. Akad.
  Wetensch., Proc. (1949), 14-17 = Indagationes Math. 11 (1949), 46-49.
  [PDF](https://www.renyi.hu/~p_erdos/1949-13.pdf)
-/

@[expose] public section

open Filter
open scoped ENNReal

namespace Erdos1221

/-- The first `n` points `a 0, …, a (n - 1)` of the sequence `a`, reduced modulo `1`, that is,
as points of the circle $\mathbb{R}/\mathbb{Z}$ of circumference $1$, in the form of a function on
`Fin n`. -/
noncomputable def pts (a : ℕ → ℝ) (n : ℕ) : Fin n → ℝ := fun j => Int.fract (a j)

/-- The points `pts a n` in non-decreasing order, so `sortedPoint a n i` is the `i`-th smallest
(counted from `0`). Repeated points are kept with their multiplicity. -/
noncomputable def sortedPoint (a : ℕ → ℝ) (n : ℕ) : Fin n → ℝ :=
  pts a n ∘ Tuple.sort (pts a n)

/-- The sorted points continued periodically to all of `ℕ`: going once around the circle adds
`1`. For `n = 0` the value is the junk value `0`. -/
noncomputable def unrolled (a : ℕ → ℝ) (n j : ℕ) : ℝ :=
  if h : 0 < n then sortedPoint a n ⟨j % n, Nat.mod_lt j h⟩ + ((j / n : ℕ) : ℝ) else 0

/-- The length of the arc that starts at the `i`-th sorted point and goes `r` points forward
around the circle (with the indices read cyclically). This is the total length of `r`
consecutive intervals determined by the first `n` points [dBEr49, §1], and the distance
$\lvert a_{i+r}-a_i\rvert$ "around the circle" of the problem. If two points coincide, the
corresponding interval has length `0`. -/
noncomputable def rSpan (a : ℕ → ℝ) (n r i : ℕ) : ℝ := unrolled a n (i + r) - unrolled a n i

/-- $M_n^{(r)}(a)$: the largest `r`-span of the first `n` points of `a`. For `n ≥ 1` this is a
maximum over the `n` starting points. For `n = 0` it is the junk value `0`. -/
noncomputable def maxSpan (a : ℕ → ℝ) (n r : ℕ) : ℝ := ⨆ i : Fin n, rSpan a n r i

/-- $m_n^{(r)}(a)$: the smallest `r`-span of the first `n` points of `a`. For `n ≥ 1` this is a
minimum over the `n` starting points. For `n = 0` it is the junk value `0`. -/
noncomputable def minSpan (a : ℕ → ℝ) (n r : ℕ) : ℝ := ⨅ i : Fin n, rSpan a n r i

/-- $\Lambda_r=\inf_a\limsup_n nM_n^{(r)}(a)$, where $a$ runs over all sequences of reals (read
modulo $1$) whose points `Int.fract (a k)` are pairwise distinct, so that the first $n$ points
define $n$ intervals [dBEr49, §1]. The $\inf$ and $\limsup$ are taken in `ℝ≥0∞`, so a sequence
with unbounded $nM_n^{(r)}(a)$ contributes $\infty$. -/
noncomputable def bigLambda (r : ℕ) : ℝ≥0∞ :=
  ⨅ (a : ℕ → ℝ) (_ : Function.Injective fun k ↦ Int.fract (a k)),
    limsup (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * maxSpan a n r)) atTop

/-- $\lambda_r=\sup_a\liminf_n nm_n^{(r)}(a)$, where $a$ runs over all sequences of reals (read
modulo $1$) whose points `Int.fract (a k)` are pairwise distinct. The $\sup$ and $\liminf$ are
taken in `ℝ≥0∞`. -/
noncomputable def smallLambda (r : ℕ) : ℝ≥0∞ :=
  ⨆ (a : ℕ → ℝ) (_ : Function.Injective fun k ↦ Int.fract (a k)),
    liminf (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * minSpan a n r)) atTop

/-- $\mu_r=\inf_a\limsup_n M_n^{(r)}(a)/m_n^{(r)}(a)$, where $a$ runs over all sequences of reals
(read modulo $1$) whose points `Int.fract (a k)` are pairwise distinct. The $\inf$ and $\limsup$
are taken in `ℝ≥0∞`. For such $a$, $n\geq1$ and $r\geq1$ both spans are positive, so the
quotient is a positive real number. -/
noncomputable def mu (r : ℕ) : ℝ≥0∞ :=
  ⨅ (a : ℕ → ℝ) (_ : Function.Injective fun k ↦ Int.fract (a k)),
    limsup (fun n : ℕ => ENNReal.ofReal (maxSpan a n r) / ENNReal.ofReal (minSpan a n r)) atTop

/--
De Bruijn and Erdős [dBEr49, §§2-5] proved that $\Lambda_1=\frac{1}{\log 2}$,
$\lambda_1=\frac{1}{\log 4}$, and $\mu_1=2$. A sequence which witnesses this is
$a_k=\log_2(2k-1)$. For $r=1$ the normalisation by $r$ plays no role.
-/
theorem erdos_1221.variants.r_one :
    bigLambda 1 = ENNReal.ofReal (1 / Real.log 2) ∧
      smallLambda 1 = ENNReal.ofReal (1 / Real.log 4) ∧ mu 1 = 2 := by
  sorry

end Erdos1221

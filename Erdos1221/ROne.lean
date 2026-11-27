module

public import Erdos1221.Defs


/-!
# Erdős Problem 1221, the case `r = 1`

A proof of `Erdos1221.erdos_1221.variants.r_one` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures):
de Bruijn and Erdős [dBEr49] showed `Λ₁ = 1/log 2`, `λ₁ = 1/log 4` and `μ₁ = 2`.

* Upper half: the sequence `a k = log₂ (2k + 1)`. Its first `n` points correspond to the integers
  `n, …, 2n - 1`, so every span lies between `log₂ (1 + 1/(2n-1))` and `log₂ (1 + 1/n)`.
* `μ₁ ≥ 2`: a new point halves some interval, so `2 m_{k+1} ≤ M_k`; then `M_k ≤ c M_{k-1}`
  with `c < 1` would contradict `M_k ≥ 1/k`.
* `Λ₁ ≥ 1/log 2`: the `t` new points `a n, …, a (n+t-1)` enter at most `t` arcs of time `n`,
  so the `t`-th largest arc is at most `M_{n+t}`, and `1 ≤ ∑_{t<n} M_{n+t}`.
* `λ₁ ≤ 1/log 4`: at time `2n` at most `2t` arcs have an endpoint born after time `2n - t`,
  and the other arcs are at least `m_{2n-t}`, so `2 ∑_{t<n} m_{2n-t} ≤ 1`.

[dBEr49] N. G. de Bruijn and P. Erdős, *Sequences of points on a circle*,
Indagationes Math. 11 (1949), 46–49.
-/

@[expose] public section

open Filter Erdos1221
open scoped ENNReal

namespace Erdos1221.ROne

variable {a : ℕ → ℝ} {n : ℕ}

lemma fract_sub_fract (x y : ℝ) : Int.fract (Int.fract x - Int.fract y) = Int.fract (x - y) := by
  have : Int.fract x - Int.fract y = (x - y) - ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) := by
    simp only [Int.fract]; push_cast; ring
  rw [this, Int.fract_sub_intCast]

lemma pts_injective (ha : Function.Injective fun k ↦ Int.fract (a k)) :
    Function.Injective (pts a n) := fun _ _ h => Fin.ext (ha h)

lemma sortedPoint_strictMono (ha : Function.Injective fun k ↦ Int.fract (a k)) :
    StrictMono (sortedPoint a n) :=
  (Tuple.monotone_sort (pts a n)).strictMono_of_injective
    ((pts_injective ha).comp (Tuple.sort (pts a n)).injective)

lemma sortedPoint_mem (i : Fin n) : 0 ≤ sortedPoint a n i ∧ sortedPoint a n i < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

lemma sortedPoint_eq (i : Fin n) :
    sortedPoint a n i = Int.fract (a (Tuple.sort (pts a n) i)) := rfl

lemma unrolled_of_lt {i : ℕ} (hi : i < n) : unrolled a n i = sortedPoint a n ⟨i, hi⟩ := by
  have hn : 0 < n := by omega
  simp [unrolled, hn, Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi]

lemma unrolled_n (hn : 0 < n) : unrolled a n n = sortedPoint a n ⟨0, hn⟩ + 1 := by
  simp [unrolled, hn, Nat.div_self hn]

/-- The `1`-span at `i` is at most the forward distance to any other sorted point. -/
lemma rSpan_le (ha : Function.Injective fun k ↦ Int.fract (a k)) (i k : Fin n) (hki : k ≠ i) :
    rSpan a n 1 i ≤ Int.fract (sortedPoint a n k - sortedPoint a n i) := by
  have hmono := sortedPoint_strictMono (n := n) ha
  have hi := sortedPoint_mem (a := a) i
  have hk := sortedPoint_mem (a := a) k
  unfold rSpan
  rw [unrolled_of_lt i.2]
  rcases lt_or_gt_of_ne hki with h | h
  · -- `k < i`: the forward distance wraps around.
    have hlt : sortedPoint a n k < sortedPoint a n i := hmono h
    have hf : Int.fract (sortedPoint a n k - sortedPoint a n i) =
        sortedPoint a n k - sortedPoint a n i + 1 := by
      rw [← Int.fract_add_one, Int.fract_eq_self]; constructor <;> linarith
    rw [hf]
    by_cases hi1 : (i : ℕ) + 1 < n
    · rw [unrolled_of_lt hi1]
      have := (sortedPoint_mem (a := a) ⟨i + 1, hi1⟩).2
      linarith
    · have hn : 0 < n := by omega
      have : (i : ℕ) + 1 = n := by omega
      rw [this, unrolled_n hn]
      have : sortedPoint a n ⟨0, hn⟩ ≤ sortedPoint a n k :=
        hmono.monotone (Fin.mk_le_mk.mpr (Nat.zero_le _))
      linarith
  · -- `i < k`: the next point is at most `k`.
    have hlt : sortedPoint a n i < sortedPoint a n k := hmono h
    have hf : Int.fract (sortedPoint a n k - sortedPoint a n i) =
        sortedPoint a n k - sortedPoint a n i := by
      rw [Int.fract_eq_self]; constructor <;> linarith
    rw [hf]
    have hi1 : (i : ℕ) + 1 < n := by have := k.2; have : (i : ℕ) < k := h; omega
    rw [unrolled_of_lt hi1]
    have : sortedPoint a n ⟨i + 1, hi1⟩ ≤ sortedPoint a n k :=
      hmono.monotone (Fin.mk_le_mk.mpr (by have : (i : ℕ) < k := h; omega))
    linarith

/-- For `n ≥ 2`, the `1`-span at `i` is the forward distance to some other sorted point. -/
lemma exists_rSpan_eq (ha : Function.Injective fun k ↦ Int.fract (a k)) (hn : 2 ≤ n) (i : Fin n) :
    ∃ k : Fin n, k ≠ i ∧ rSpan a n 1 i = Int.fract (sortedPoint a n k - sortedPoint a n i) := by
  have hmono := sortedPoint_strictMono (n := n) ha
  have hi := sortedPoint_mem (a := a) i
  unfold rSpan
  rw [unrolled_of_lt i.2]
  by_cases hi1 : (i : ℕ) + 1 < n
  · refine ⟨⟨i + 1, hi1⟩, fun h => by simp [Fin.ext_iff] at h, ?_⟩
    rw [unrolled_of_lt hi1]
    have hlt : sortedPoint a n i < sortedPoint a n ⟨i + 1, hi1⟩ :=
      hmono (Fin.mk_lt_mk.mpr (by omega))
    have := (sortedPoint_mem (a := a) ⟨i + 1, hi1⟩).2
    rw [eq_comm, Int.fract_eq_self]; constructor <;> linarith
  · have hn0 : 0 < n := by omega
    have : (i : ℕ) + 1 = n := by omega
    refine ⟨⟨0, hn0⟩, fun h => by simp [Fin.ext_iff] at h; omega, ?_⟩
    rw [this, unrolled_n hn0]
    have hlt : sortedPoint a n ⟨0, hn0⟩ < sortedPoint a n i :=
      hmono (Fin.mk_lt_mk.mpr (by omega))
    have := (sortedPoint_mem (a := a) ⟨0, hn0⟩).1
    simp only [Fin.eta]
    rw [eq_comm, ← Int.fract_add_one,
      show sortedPoint a n ⟨0, hn0⟩ + 1 - sortedPoint a n i =
        sortedPoint a n ⟨0, hn0⟩ - sortedPoint a n i + 1 by ring, Int.fract_eq_self]
    constructor <;> linarith

/- ### The witness sequence -/

/-- The witness `a k = log₂ (2k + 1)` of [dBEr49, §2] (indexed from `0`). -/
noncomputable def w (k : ℕ) : ℝ := Real.logb 2 (2 * k + 1)

/-- Every `x` with `0 < x < 2n` has a multiple `x * 2 ^ t` in `[n, 2n)`. -/
lemma exists_rep {x n : ℕ} (hx : 0 < x) (hxn : x < 2 * n) :
    ∃ t : ℕ, n ≤ x * 2 ^ t ∧ x * 2 ^ t < 2 * n := by
  classical
  have hex : ∃ t, n ≤ x * 2 ^ t :=
    ⟨n, (Nat.lt_two_pow_self).le.trans (Nat.le_mul_of_pos_left _ hx)⟩
  obtain ⟨T, hT⟩ : ∃ T, T = Nat.find hex := ⟨_, rfl⟩
  have hspec : n ≤ x * 2 ^ T := hT ▸ Nat.find_spec hex
  have hmin : ∀ t < T, ¬ n ≤ x * 2 ^ t := fun t ht => Nat.find_min hex (hT ▸ ht)
  refine ⟨T, hspec, ?_⟩
  cases T with
  | zero => simpa using hxn
  | succ t =>
    have := hmin t (Nat.lt_succ_self t)
    rw [show x * 2 ^ (t + 1) = 2 * (x * 2 ^ t) by ring]
    omega

lemma logb_mul_two_pow {x : ℝ} (hx : 0 < x) (t : ℕ) :
    Real.logb 2 (x * 2 ^ t) = Real.logb 2 x + t := by
  rw [Real.logb_mul hx.ne' (by positivity), Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  ring

/-- The forward distance from `w j` to `w k` only depends on representatives. -/
lemma fract_w_sub (j k t s : ℕ) :
    Int.fract (w k - w j) =
      Int.fract (Real.logb 2 (((2 * k + 1) * 2 ^ s : ℕ) : ℝ) -
        Real.logb 2 (((2 * j + 1) * 2 ^ t : ℕ) : ℝ)) := by
  push_cast
  rw [logb_mul_two_pow (x := 2 * (k : ℝ) + 1) (by positivity),
    logb_mul_two_pow (x := 2 * (j : ℝ) + 1) (by positivity),
    show Real.logb 2 (2 * k + 1) + s - (Real.logb 2 (2 * j + 1) + t) =
      (w k - w j) + ((s - t : ℤ) : ℝ) by unfold w; push_cast; ring, Int.fract_add_intCast]

lemma odd_eq_of_mul_two_pow {x y t s : ℕ} (hx : Odd x) (hy : Odd y)
    (h : x * 2 ^ t = y * 2 ^ s) : x = y := by
  wlog hts : t ≤ s generalizing x y t s
  · exact (this hy hx h.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hts
  have h2 : x * 2 ^ t = (y * 2 ^ d) * 2 ^ t := by rw [h]; ring
  have h' := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos t) h2
  rcases d with _ | d
  · simpa using h'
  · rw [pow_succ] at h'
    exact absurd (h' ▸ ⟨2 ^ d * y, by ring⟩ : Even x) (Nat.not_even_iff_odd.mpr hx)

lemma two_n_div_le {n : ℕ} (hn : 1 ≤ n) :
    (2 * n : ℝ) / (2 * n - 1) ≤ 1 + 1 / n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_iff₀ (by linarith)]
  field_simp
  nlinarith

/-- Distinct points of the witness are at forward distance at least `log₂ (2n/(2n-1))`. -/
lemma le_fract_w_sub {n j k : ℕ} (hj : j < n) (hk : k < n) (hjk : j ≠ k) :
    Real.logb 2 ((2 * n : ℝ) / (2 * n - 1)) ≤ Int.fract (w k - w j) := by
  obtain ⟨t, ht1, ht2⟩ := exists_rep (x := 2 * j + 1) (n := n) (by omega) (by omega)
  obtain ⟨s, hs1, hs2⟩ := exists_rep (x := 2 * k + 1) (n := n) (by omega) (by omega)
  rw [fract_w_sub j k t s]
  set u := (2 * j + 1) * 2 ^ t
  set v := (2 * k + 1) * 2 ^ s
  have huv : u ≠ v := fun h => hjk (by
    have := odd_eq_of_mul_two_pow (by simp) (by simp) h; omega)
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hu1 : (n : ℝ) ≤ u := by exact_mod_cast ht1
  have hu2 : (u : ℝ) ≤ 2 * n - 1 := by
    have : u + 1 ≤ 2 * n := ht2; have : ((u + 1 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hv1 : (n : ℝ) ≤ v := by exact_mod_cast hs1
  have hv2 : (v : ℝ) ≤ 2 * n - 1 := by
    have : v + 1 ≤ 2 * n := hs2; have : ((v + 1 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  rw [← Real.logb_div hv0.ne' hu0.ne']
  rcases lt_or_gt_of_ne huv with h | h
  · -- `u < v`
    have h' : (u : ℝ) + 1 ≤ v := by exact_mod_cast h
    have hlt : Real.logb 2 ((v : ℝ) / u) < 1 := by
      rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity), Real.rpow_one,
        div_lt_iff₀ hu0]; linarith
    have hpos : 0 ≤ Real.logb 2 ((v : ℝ) / u) :=
      Real.logb_nonneg (by norm_num) ((one_le_div hu0).mpr (by linarith))
    rw [(Int.fract_eq_self).mpr ⟨hpos, hlt⟩]
    apply Real.logb_le_logb_of_le (by norm_num) (div_pos (by linarith) (by linarith))
    rw [div_le_div_iff₀ (by linarith) hu0]
    nlinarith
  · -- `v < u`: the distance wraps around
    have h' : (v : ℝ) + 1 ≤ u := by exact_mod_cast h
    have heq : Real.logb 2 ((v : ℝ) / u) + 1 = Real.logb 2 (2 * v / u) := by
      rw [mul_div_assoc, Real.logb_mul (by norm_num) (by positivity),
        Real.logb_self_eq_one (by norm_num)]; ring
    have hlt : Real.logb 2 (2 * (v : ℝ) / u) < 1 := by
      rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity), Real.rpow_one,
        div_lt_iff₀ hu0]; linarith
    have hpos : 0 ≤ Real.logb 2 (2 * (v : ℝ) / u) :=
      Real.logb_nonneg (by norm_num) ((one_le_div hu0).mpr (by linarith))
    rw [← Int.fract_add_one, heq, (Int.fract_eq_self).mpr ⟨hpos, hlt⟩]
    apply Real.logb_le_logb_of_le (by norm_num) (div_pos (by linarith) (by linarith))
    rw [div_le_div_iff₀ (by linarith) hu0]
    nlinarith

lemma injective_w : Function.Injective fun k ↦ Int.fract (w k) := by
  intro j k h
  by_contra hjk
  have := le_fract_w_sub (n := max j k + 1) (by omega) (by omega) hjk
  rw [← fract_sub_fract, show Int.fract (w k) = Int.fract (w j) from h.symm, sub_self,
    Int.fract_zero] at this
  have hpos : 0 < Real.logb 2 ((2 * ((max j k + 1 : ℕ) : ℝ)) / (2 * ((max j k + 1 : ℕ) : ℝ) - 1)) := by
    apply Real.logb_pos (by norm_num)
    have : (1 : ℝ) ≤ ((max j k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ max j k + 1 by omega)
    rw [one_lt_div (by linarith)]; linarith
  push_cast at this hpos
  linarith

/-- Every point of the witness has another point at forward distance at most `log₂ (1 + 1/n)`. -/
lemma exists_fract_w_sub_le {n j : ℕ} (hn : 2 ≤ n) (hj : j < n) :
    ∃ k < n, k ≠ j ∧ Int.fract (w k - w j) ≤ Real.logb 2 (1 + 1 / n) := by
  obtain ⟨t, ht1, ht2⟩ := exists_rep (x := 2 * j + 1) (n := n) (by omega) (by omega)
  set u := (2 * j + 1) * 2 ^ t with hu
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hu1 : (n : ℝ) ≤ u := by exact_mod_cast ht1
  have hu0 : (0 : ℝ) < u := by linarith
  -- The next point, as a number `V` in `(u, 2u)` (or `2V` when wrapping around).
  obtain ⟨V, hV0, hV2, hval, hpos, hle⟩ : ∃ V : ℕ, 0 < V ∧ V < 2 * n ∧
      Int.fract (Real.logb 2 (V : ℝ) - Real.logb 2 (u : ℝ)) =
        Real.logb 2 (if u + 1 < 2 * n then ((u : ℝ) + 1) / u else 2 * (n : ℝ) / (2 * n - 1)) ∧
      0 < Real.logb 2 (if u + 1 < 2 * n then ((u : ℝ) + 1) / u else 2 * (n : ℝ) / (2 * n - 1)) ∧
      Real.logb 2 (if u + 1 < 2 * n then ((u : ℝ) + 1) / u else 2 * (n : ℝ) / (2 * n - 1)) ≤
        Real.logb 2 (1 + 1 / n) := by
    by_cases hc : u + 1 < 2 * n
    · refine ⟨u + 1, by omega, hc, ?_, ?_, ?_⟩ <;> simp only [hc, ite_true]
      · push_cast
        rw [← Real.logb_div (by positivity) hu0.ne']
        have hlt : Real.logb 2 (((u : ℝ) + 1) / u) < 1 := by
          rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity), Real.rpow_one,
            div_lt_iff₀ hu0]; linarith
        exact (Int.fract_eq_self).mpr ⟨(Real.logb_pos (by norm_num)
          ((one_lt_div hu0).mpr (by linarith))).le, hlt⟩
      · exact Real.logb_pos (by norm_num) ((one_lt_div hu0).mpr (by linarith))
      · apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
        rw [add_div, div_self hu0.ne', add_le_add_iff_left]
        exact one_div_le_one_div_of_le (by linarith) hu1
    · have hu' : (u : ℝ) = 2 * n - 1 := by
        have : u + 1 = 2 * n := by omega
        have : ((u + 1 : ℕ) : ℝ) = ((2 * n : ℕ) : ℝ) := by rw [this]
        push_cast at this; linarith
      refine ⟨n, by omega, by omega, ?_, ?_, ?_⟩ <;> simp only [hc, ite_false]
      · rw [← Real.logb_div (by positivity) hu0.ne', hu', ← Int.fract_add_one]
        have heq : Real.logb 2 ((n : ℝ) / (2 * n - 1)) + 1 =
            Real.logb 2 (2 * (n : ℝ) / (2 * n - 1)) := by
          rw [mul_div_assoc, Real.logb_mul (by norm_num) (div_pos (by linarith) (by linarith)).ne',
            Real.logb_self_eq_one (by norm_num)]; ring
        rw [heq]
        have hlt : Real.logb 2 (2 * (n : ℝ) / (2 * n - 1)) < 1 := by
          rw [Real.logb_lt_iff_lt_rpow (by norm_num) (div_pos (by linarith) (by linarith)),
            Real.rpow_one, div_lt_iff₀ (by linarith)]; linarith
        exact (Int.fract_eq_self).mpr ⟨(Real.logb_pos (by norm_num)
          ((one_lt_div (by linarith)).mpr (by linarith))).le, hlt⟩
      · exact Real.logb_pos (by norm_num) ((one_lt_div (by linarith)).mpr (by linarith))
      · exact Real.logb_le_logb_of_le (by norm_num) (div_pos (by linarith) (by linarith))
          (two_n_div_le (by omega))
  -- Write `V = 2 ^ s * (2k + 1)`.
  obtain ⟨s, y, hy, hVy⟩ := Nat.exists_eq_two_pow_mul_odd (n := V) hV0.ne'
  obtain ⟨k, rfl⟩ := hy
  have hk : k < n := by
    have : 2 ^ s * (2 * k + 1) ≥ 2 * k + 1 := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos s)
    omega
  have hfr : Int.fract (w k - w j) = Real.logb 2
      (if u + 1 < 2 * n then ((u : ℝ) + 1) / u else 2 * (n : ℝ) / (2 * n - 1)) := by
    rw [fract_w_sub j k t s, ← hval, ← hu, show (2 * k + 1) * 2 ^ s = V by rw [hVy]; ring]
  refine ⟨k, hk, fun hkj => ?_, hfr ▸ hle⟩
  subst hkj
  rw [sub_self, Int.fract_zero] at hfr
  linarith

lemma maxSpan_le {n : ℕ} (hn : 2 ≤ n) : maxSpan w n 1 ≤ Real.logb 2 (1 + 1 / n) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ciSup_le fun i => ?_
  set σ := Tuple.sort (pts w n)
  obtain ⟨k, hk, hkj, hle⟩ := exists_fract_w_sub_le hn (σ i).2
  set K := σ.symm ⟨k, hk⟩
  have hKi : K ≠ i := fun h => hkj (by
    have := congrArg σ h; simp [K] at this; rw [← this])
  refine (rSpan_le ?_ i K hKi).trans ?_
  · exact injective_w
  rw [sortedPoint_eq, sortedPoint_eq, fract_sub_fract]
  simpa [K, σ, pts] using hle

lemma le_minSpan {n : ℕ} (hn : 2 ≤ n) :
    Real.logb 2 ((2 * n : ℝ) / (2 * n - 1)) ≤ minSpan w n 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine le_ciInf fun i => ?_
  set σ := Tuple.sort (pts w n)
  obtain ⟨K, hKi, heq⟩ := exists_rSpan_eq injective_w hn i
  rw [heq, sortedPoint_eq, sortedPoint_eq, fract_sub_fract]
  exact le_fract_w_sub (σ i).2 (σ K).2 fun h => hKi (σ.injective (Fin.ext h)).symm

/- ### Elementary inequalities -/

lemma log_le_inv {n : ℕ} (hn : 1 ≤ n) : Real.log (1 + 1 / n) ≤ 1 / n := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / n by positivity)]

lemma inv_two_le_log {n : ℕ} (hn : 1 ≤ n) :
    1 / (2 * n : ℝ) ≤ Real.log ((2 * n : ℝ) / (2 * n - 1)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (2 * n : ℝ) / (2 * n - 1) := div_pos (by linarith) (by linarith)
  have h := Real.one_sub_inv_le_log_of_pos hpos
  rw [inv_div] at h
  have : 1 - (2 * (n : ℝ) - 1) / (2 * n) = 1 / (2 * n) := by field_simp; ring
  linarith

lemma log_two_pos' : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

lemma n_mul_maxSpan_le {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) * maxSpan w n 1 ≤ 1 / Real.log 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc (n : ℝ) * maxSpan w n 1 ≤ n * (Real.log (1 + 1 / n) / Real.log 2) :=
        mul_le_mul_of_nonneg_left (maxSpan_le hn) hn0.le
    _ ≤ n * ((1 / n) / Real.log 2) := by
        gcongr; exact log_le_inv (by omega)
    _ = 1 / Real.log 2 := by field_simp

lemma le_n_mul_minSpan {n : ℕ} (hn : 2 ≤ n) : 1 / Real.log 4 ≤ (n : ℝ) * minSpan w n 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  calc 1 / Real.log 4 = n * ((1 / (2 * n)) / Real.log 2) := by
        rw [h4]; field_simp
    _ ≤ n * (Real.log ((2 * n : ℝ) / (2 * n - 1)) / Real.log 2) := by
        gcongr; exact inv_two_le_log (by omega)
    _ ≤ (n : ℝ) * minSpan w n 1 := mul_le_mul_of_nonneg_left (le_minSpan hn) hn0.le

lemma maxSpan_le_two_mul {n : ℕ} (hn : 2 ≤ n) : maxSpan w n 1 ≤ 2 * minSpan w n 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc maxSpan w n 1 ≤ Real.log (1 + 1 / n) / Real.log 2 := maxSpan_le hn
    _ ≤ (1 / n) / Real.log 2 := by gcongr; exact log_le_inv (by omega)
    _ = 2 * ((1 / (2 * n)) / Real.log 2) := by field_simp
    _ ≤ 2 * (Real.log ((2 * n : ℝ) / (2 * n - 1)) / Real.log 2) := by
        gcongr; exact inv_two_le_log (by omega)
    _ ≤ 2 * minSpan w n 1 := by gcongr; exact le_minSpan hn

/- ### The upper half of `r_one` -/

theorem bigLambda_one_le : bigLambda 1 ≤ ENNReal.ofReal (1 / Real.log 2) :=
  (iInf₂_le w injective_w).trans <| limsup_le_of_le (by isBoundedDefault) <|
    eventually_atTop.2 ⟨2, fun _ hn => ENNReal.ofReal_le_ofReal (n_mul_maxSpan_le hn)⟩

theorem le_smallLambda_one : ENNReal.ofReal (1 / Real.log 4) ≤ smallLambda 1 :=
  le_iSup₂_of_le w injective_w <| le_liminf_of_le (by isBoundedDefault) <|
    eventually_atTop.2 ⟨2, fun _ hn => ENNReal.ofReal_le_ofReal (le_n_mul_minSpan hn)⟩

theorem mu_one_le : mu 1 ≤ 2 :=
  (iInf₂_le w injective_w).trans <| limsup_le_of_le (by isBoundedDefault) <|
    eventually_atTop.2 ⟨2, fun _ hn => ENNReal.div_le_of_le_mul (by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (maxSpan_le_two_mul hn))⟩

/- ### General facts about the spans, phrased through the points `Int.fract (a j)` -/

section General

variable (ha : Function.Injective fun k ↦ Int.fract (a k))
include ha

/-- The sorted index of the point `a j` among the first `n` points. -/
noncomputable def idx (a : ℕ → ℝ) (n : ℕ) (j : Fin n) : Fin n := (Tuple.sort (pts a n)).symm j

omit ha in
lemma sortedPoint_idx (j : Fin n) : sortedPoint a n (idx a n j) = Int.fract (a j) := by
  simp [idx, sortedPoint, pts]

lemma fract_sub_pos {i j : ℕ} (hij : i ≠ j) : 0 < Int.fract (a j - a i) := by
  rcases (Int.fract_nonneg (a j - a i)).lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← fract_sub_fract] at h
    have hi := Int.fract_nonneg (a i); have hi' := Int.fract_lt_one (a i)
    have hj := Int.fract_nonneg (a j); have hj' := Int.fract_lt_one (a j)
    rcases le_or_gt 0 (Int.fract (a j) - Int.fract (a i)) with hd | hd
    · rw [Int.fract_eq_self.mpr ⟨hd, by linarith⟩] at h
      exact hij (ha (show Int.fract (a i) = Int.fract (a j) by linarith))
    · rw [← Int.fract_add_one, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] at h
      linarith

lemma rSpan_le_val {j₁ j₂ : Fin n} (hj : j₁ ≠ j₂) :
    rSpan a n 1 (idx a n j₁) ≤ Int.fract (a j₂ - a j₁) := by
  have := rSpan_le ha (idx a n j₁) (idx a n j₂)
    (fun h => hj ((Tuple.sort (pts a n)).symm.injective h).symm)
  rwa [sortedPoint_idx, sortedPoint_idx, fract_sub_fract] at this

lemma exists_rSpan_eq_val (hn : 2 ≤ n) (i : Fin n) :
    ∃ j₁ j₂ : Fin n, j₁ ≠ j₂ ∧ i = idx a n j₁ ∧ rSpan a n 1 i = Int.fract (a j₂ - a j₁) := by
  obtain ⟨K, hKi, heq⟩ := exists_rSpan_eq ha hn i
  set σ := Tuple.sort (pts a n)
  refine ⟨σ i, σ K, fun h => hKi (σ.injective h).symm, by simp [idx, σ], ?_⟩
  rw [heq, sortedPoint_eq, sortedPoint_eq, fract_sub_fract]

omit ha in
lemma rSpan_le_maxSpan (i : Fin n) : rSpan a n 1 i ≤ maxSpan a n 1 :=
  le_ciSup (f := fun i : Fin n => rSpan a n 1 i) (Set.finite_range _).bddAbove i

omit ha in
lemma minSpan_le_rSpan (i : Fin n) : minSpan a n 1 ≤ rSpan a n 1 i :=
  ciInf_le (f := fun i : Fin n => rSpan a n 1 i) (Set.finite_range _).bddBelow i

omit ha in
lemma sum_rSpan (hn : 0 < n) : ∑ i : Fin n, rSpan a n 1 i = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => rSpan a n 1 i)]
  unfold rSpan
  rw [Finset.sum_range_sub (fun i => unrolled a n i), unrolled_n hn,
    unrolled_of_lt hn]
  ring

omit ha in
lemma one_div_le_maxSpan (hn : 0 < n) : 1 / (n : ℝ) ≤ maxSpan a n 1 := by
  have h := sum_rSpan (a := a) hn
  have : ∑ i : Fin n, rSpan a n 1 i ≤ ∑ _i : Fin n, maxSpan a n 1 :=
    Finset.sum_le_sum fun i _ => rSpan_le_maxSpan i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  linarith

lemma rSpan_pos (i : Fin n) : 0 < rSpan a n 1 i := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hn1 : n = 1 := by have := i.2; omega
    subst hn1
    have h := sum_rSpan (a := a) Nat.one_pos
    simp only [Fin.sum_univ_one] at h
    rw [Subsingleton.elim i 0, h]; norm_num
  · obtain ⟨j₁, j₂, hj, -, heq⟩ := exists_rSpan_eq_val ha hn i
    rw [heq]
    exact fract_sub_pos ha (fun h => hj (Fin.ext h))

lemma minSpan_pos (hn : 0 < n) : 0 < minSpan a n 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i : Fin n => rSpan a n 1 i)
  rw [minSpan, ← hi]
  exact rSpan_pos ha i

lemma maxSpan_le_one (hn : 0 < n) : maxSpan a n 1 ≤ 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ciSup_le fun i => ?_
  rw [← sum_rSpan (a := a) hn]
  exact Finset.single_le_sum (f := fun i : Fin n => rSpan a n 1 i)
    (fun j _ => (rSpan_pos ha j).le) (Finset.mem_univ i)

/-- A new point splits some interval of length at most `M_k` into two parts, so
`2 m_{k+1} ≤ M_k`. -/
lemma two_mul_minSpan_succ_le {k : ℕ} (hk : 1 ≤ k) :
    2 * minSpan a (k + 1) 1 ≤ maxSpan a k 1 := by
  -- The old point `a js` closest behind the new point `a k`.
  obtain ⟨js, hjs, hmin⟩ := (Finset.range k).exists_min_image (fun j => Int.fract (a k - a j))
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  rw [Finset.mem_range] at hjs
  set β := Int.fract (a k - a js)
  have hβ1 : β < 1 := Int.fract_lt_one _
  have hβ0 : 0 ≤ β := Int.fract_nonneg _
  -- `G₁`: the new span at `a js`; `G₂`: the new span at `a k`.
  have hG₁ : rSpan a (k + 1) 1 (idx a (k + 1) ⟨js, by omega⟩) ≤ β :=
    rSpan_le_val ha (j₂ := ⟨k, by omega⟩) (by simp [Fin.ext_iff]; omega)
  have hm₁ := minSpan_le_rSpan (a := a) (n := k + 1) (idx a (k + 1) ⟨js, by omega⟩)
  have hm₂ := minSpan_le_rSpan (a := a) (n := k + 1) (idx a (k + 1) ⟨k, by omega⟩)
  have hℓM := rSpan_le_maxSpan (a := a) (n := k) (idx a k ⟨js, hjs⟩)
  set ℓ := rSpan a k 1 (idx a k ⟨js, hjs⟩)
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · -- `k = 1`: the only old interval is the whole circle.
    have hk1 : k = 1 := by omega
    subst hk1
    have hjs0 : js = 0 := by omega
    subst hjs0
    have hℓ : ℓ = 1 := by
      have h := sum_rSpan (a := a) Nat.one_pos
      simp only [Fin.sum_univ_one] at h
      simp only [ℓ]; rw [Subsingleton.elim (idx a 1 ⟨0, hjs⟩) 0, h]
    have hG₂ : rSpan a 2 1 (idx a 2 ⟨1, by omega⟩) ≤ 1 - β := by
      have h := rSpan_le_val ha (n := 2) (j₁ := ⟨1, by omega⟩) (j₂ := ⟨0, by omega⟩) (by simp)
      have hne : Int.fract (a 1 - a 0) ≠ 0 := (fract_sub_pos ha (by omega)).ne'
      simp only at h
      rwa [show a 0 - a 1 = -(a 1 - a 0) by ring, Int.fract_neg hne] at h
    linarith
  · -- `k ≥ 2`: the interval at `a js` ends at an old point `a jq`, beyond the new point.
    obtain ⟨j₁, jq, hj, hidx, hℓ⟩ := exists_rSpan_eq_val ha hk2 (idx a k ⟨js, hjs⟩)
    have hj₁ : j₁ = ⟨js, hjs⟩ := ((Tuple.sort (pts a k)).symm.injective hidx).symm
    subst hj₁
    have hℓ' : ℓ = Int.fract (a jq - a js) := hℓ
    have hℓpos : 0 < ℓ := rSpan_pos ha _
    have hℓ1 : ℓ < 1 := hℓ' ▸ Int.fract_lt_one _
    have hjq : (jq : ℕ) < k := jq.2
    have hjqs : (jq : ℕ) ≠ js := fun h => hj (Fin.ext h.symm)
    have hid1 : Int.fract (a k - a jq) = Int.fract (β - ℓ) := by
      rw [hℓ', fract_sub_fract]; congr 1; ring
    have hid2 : Int.fract (a jq - a k) = Int.fract (ℓ - β) := by
      rw [hℓ', fract_sub_fract]; congr 1; ring
    -- `β < ℓ`, by minimality of `js`.
    have hβℓ : β < ℓ := by
      by_contra hcon
      have hcon : ℓ ≤ β := not_lt.mp hcon
      have := hmin jq (Finset.mem_range.mpr hjq)
      rw [hid1, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] at this
      linarith
    have hG₂ : rSpan a (k + 1) 1 (idx a (k + 1) ⟨k, by omega⟩) ≤ ℓ - β := by
      have h := rSpan_le_val ha (n := k + 1) (j₁ := ⟨k, by omega⟩) (j₂ := ⟨jq, by omega⟩)
        (by simp [Fin.ext_iff]; omega)
      simp only at h
      rwa [hid2, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] at h
    linarith

end General

/-- The lower bound `μ₁ ≥ 2` [dBEr49, §5]. -/
theorem two_le_mu_one : 2 ≤ mu 1 := by
  refine le_iInf₂ fun a ha => ?_
  by_contra h
  have h : limsup (fun n : ℕ => ENNReal.ofReal (maxSpan a n 1) /
      ENNReal.ofReal (minSpan a n 1)) atTop < 2 := not_le.mp h
  obtain ⟨c, hc1, hc2⟩ := exists_between h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hc1 (by isBoundedDefault))
  have hct : c ≠ ⊤ := ne_top_of_lt hc2
  set c' := c.toReal
  have hc'2 : c' < 2 := by
    have := (ENNReal.toReal_lt_toReal hct (by simp)).mpr hc2
    simpa using this
  have hc'0 : 0 ≤ c' := ENNReal.toReal_nonneg
  set N₀ := max N 1
  have hN₀ : 1 ≤ N₀ := le_max_right _ _
  have hM : ∀ n ≥ N₀, maxSpan a n 1 ≤ c' * minSpan a n 1 := by
    intro n hn
    have h1 := hN n (le_of_max_le_left hn)
    have hn0 : 0 < n := by omega
    have hm := minSpan_pos ha hn0
    have hMpos : 0 ≤ maxSpan a n 1 :=
      (div_nonneg zero_le_one (Nat.cast_nonneg n)).trans (one_div_le_maxSpan hn0)
    rw [ENNReal.div_lt_iff (Or.inl (by simpa using hm)) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_toReal hct, ← ENNReal.ofReal_mul hc'0] at h1
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hMpos).mp h1).le
  set ρ := c' / 2
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by simp only [ρ]; linarith
  have hstep : ∀ n ≥ N₀, maxSpan a (n + 1) 1 ≤ ρ * maxSpan a n 1 := by
    intro n hn
    have h1 := hM (n + 1) (by omega)
    have h2 := two_mul_minSpan_succ_le ha (k := n) (by omega)
    have h3 := mul_le_mul_of_nonneg_left h2 hc'0
    simp only [ρ]; nlinarith
  have hpow : ∀ t : ℕ, maxSpan a (N₀ + t) 1 ≤ ρ ^ t := by
    intro t
    induction t with
    | zero => simpa using maxSpan_le_one ha (by omega : 0 < N₀)
    | succ t ih =>
      calc maxSpan a (N₀ + (t + 1)) 1 ≤ ρ * maxSpan a (N₀ + t) 1 :=
          hstep (N₀ + t) (Nat.le_add_right _ _)
        _ ≤ ρ * ρ ^ t := by gcongr
        _ = ρ ^ (t + 1) := by ring
  have hlim : Tendsto (fun t : ℕ => ((N₀ : ℝ) + t) * ρ ^ t) atTop (nhds 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1
    have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul (N₀ : ℝ)
    simpa [add_mul] using h2.add h1
  obtain ⟨t, ht⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists
  have h1 := one_div_le_maxSpan (a := a) (n := N₀ + t) (by omega)
  have h2 := hpow t
  have hpos : (0 : ℝ) < N₀ + t := by positivity
  push_cast at h1
  rw [div_le_iff₀ hpos] at h1
  nlinarith

/- ### The lower bound `Λ₁ ≥ 1/log 2` -/

section BigLambda

variable (ha : Function.Injective fun k ↦ Int.fract (a k))
include ha

/-- The span at the point `a j` among the first `n` points. -/
noncomputable def gap (a : ℕ → ℝ) (n : ℕ) (j : Fin n) : ℝ := rSpan a n 1 (idx a n j)

/-- A real `x` lies in the half-open arc `[a j, a j + gap j)` for at most one old point `j`. -/
lemma arc_unique {j j' : Fin n} (hjj' : j ≠ j') (x : ℝ)
    (h₁ : Int.fract (x - a j) < gap a n j) (h₂ : Int.fract (x - a j') < gap a n j') : False := by
  have hα := rSpan_le_val ha hjj'
  have hα' := rSpan_le_val ha hjj'.symm
  change gap a n j ≤ _ at hα
  change gap a n j' ≤ _ at hα'
  set α := Int.fract (a j' - a j)
  have hαpos : 0 < α := fract_sub_pos ha (fun h => hjj' (Fin.ext h))
  have hneg : Int.fract (a j - a j') = 1 - α := by
    rw [show a j - a j' = -(a j' - a j) by ring, Int.fract_neg hαpos.ne']
  set β := Int.fract (x - a j)
  have hβ0 : 0 ≤ β := Int.fract_nonneg _
  have hγ : Int.fract (x - a j') = β - α + 1 := by
    rw [show x - a j' = (x - a j) - (a j' - a j) by ring, ← fract_sub_fract,
      ← Int.fract_add_one, Int.fract_eq_self]
    have := Int.fract_lt_one (a j' - a j)
    constructor <;> linarith
  rw [hγ] at h₂
  rw [hneg] at hα'
  linarith

/-- An arc that no new point enters survives, so its length is at most the later maximal span. -/
lemma gap_le_maxSpan_of_survives {N : ℕ} (hnN : n ≤ N) (hn : 1 ≤ n) (j : Fin n)
    (hsurv : ∀ m, n ≤ m → m < N → gap a n j ≤ Int.fract (a m - a j)) :
    gap a n j ≤ maxSpan a N 1 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hn1 : n = 1 := by omega
    have hN1 : N = 1 := by omega
    subst hn1; subst hN1
    exact rSpan_le_maxSpan _
  obtain ⟨j₁, q, hq, hidx, heq⟩ := exists_rSpan_eq_val ha hN (idx a N ⟨j, by omega⟩)
  have hj₁ : j₁ = ⟨j, by omega⟩ := ((Tuple.sort (pts a N)).symm.injective hidx).symm
  rw [hj₁] at heq hq
  have hfin : gap a n j ≤ Int.fract (a q - a j) := by
    rcases Nat.lt_or_ge (q : ℕ) n with hqn | hqn
    · exact rSpan_le_val ha (j₂ := ⟨q, hqn⟩)
        (fun h => hq (Fin.ext (by simpa using congrArg Fin.val h)))
    · exact hsurv q hqn q.2
  calc gap a n j ≤ Int.fract (a q - a j) := hfin
    _ = rSpan a N 1 (idx a N ⟨j, by omega⟩) := heq.symm
    _ ≤ maxSpan a N 1 := rSpan_le_maxSpan _

omit ha in
lemma sum_gap (hn : 0 < n) : ∑ j : Fin n, gap a n j = 1 := by
  rw [← sum_rSpan (a := a) hn]
  exact Equiv.sum_comp (Tuple.sort (pts a n)).symm (fun i => rSpan a n 1 i)

/-- The `t`-th largest arc at time `n` is at most `M_{n+t}`: the `t` new points
`a n, …, a (n+t-1)` enter at most `t` of the `t + 1` largest arcs. -/
lemma gap_sort_le (hn : 1 ≤ n) {t : ℕ} (ht : t < n) :
    gap a n (Tuple.sort (gap a n) ⟨n - 1 - t, by omega⟩) ≤ maxSpan a (n + t) 1 := by
  classical
  set τ := Tuple.sort (gap a n)
  have hmono : Monotone (gap a n ∘ τ) := Tuple.monotone_sort _
  -- The `t + 1` largest arcs.
  set T : Finset (Fin n) := Finset.univ.image (fun s : Fin (t + 1) => τ ⟨n - 1 - t + s, by omega⟩)
  have hT : T.card = t + 1 := by
    rw [Finset.card_image_of_injective _ (fun s s' h => by
      have := congrArg Fin.val (τ.injective h); simp at this; exact Fin.ext (by omega))]
    simp
  -- The arcs entered by a new point.
  set K : Finset (Fin n) := Finset.univ.filter
    (fun j => ∃ m, n ≤ m ∧ m < n + t ∧ Int.fract (a m - a j) < gap a n j)
  have hK : K.card ≤ t := by
    have key : ∀ j ∈ K, ∃ m, n ≤ m ∧ m < n + t ∧ Int.fract (a m - a j) < gap a n j :=
      fun j hj => (Finset.mem_filter.mp hj).2
    choose! f hf using key
    calc K.card ≤ (Finset.Ico n (n + t)).card := by
          refine Finset.card_le_card_of_injOn f (fun j hj => ?_) (fun j hj j' hj' hjj' => ?_)
          · obtain ⟨h1, h2, -⟩ := hf j hj; simp; omega
          · by_contra hne
            obtain ⟨-, -, h1⟩ := hf j hj
            obtain ⟨-, -, h2⟩ := hf j' hj'
            rw [hjj'] at h1
            exact arc_unique ha hne _ h1 h2
      _ = t := by simp
  obtain ⟨j, hj⟩ : (T \ K).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.le_card_sdiff K T
    omega
  obtain ⟨hjT, hjK⟩ := Finset.mem_sdiff.mp hj
  have hsurv : ∀ m, n ≤ m → m < n + t → gap a n j ≤ Int.fract (a m - a j) := by
    intro m h1 h2
    by_contra hlt
    exact hjK (Finset.mem_filter.mpr ⟨Finset.mem_univ _, m, h1, h2, not_le.mp hlt⟩)
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hjT
  calc gap a n (τ ⟨n - 1 - t, by omega⟩)
      ≤ gap a n (τ ⟨n - 1 - t + s, by omega⟩) :=
        hmono (Fin.mk_le_mk.mpr (Nat.le_add_right _ _))
    _ ≤ maxSpan a (n + t) 1 := gap_le_maxSpan_of_survives ha (by omega) hn _ hsurv

lemma one_le_sum_maxSpan (hn : 1 ≤ n) : 1 ≤ ∑ t ∈ Finset.range n, maxSpan a (n + t) 1 := by
  rw [← sum_gap (a := a) (by omega : 0 < n),
    ← Equiv.sum_comp (Fin.revPerm.trans (Tuple.sort (gap a n))) (gap a n),
    ← Fin.sum_univ_eq_sum_range (fun t => maxSpan a (n + t) 1)]
  refine Finset.sum_le_sum fun t _ => ?_
  have := gap_sort_le ha hn (t := t) t.2
  have e : Fin.rev t = ⟨n - 1 - t, by omega⟩ := Fin.ext (by simp only [Fin.val_rev]; omega)
  simp only [Equiv.trans_apply, Fin.revPerm_apply, e]
  exact this

end BigLambda

lemma inv_le_log_sub {m : ℝ} (hm : 2 ≤ m) : 1 / m ≤ Real.log m - Real.log (m - 1) := by
  have hpos : 0 < m / (m - 1) := div_pos (by linarith) (by linarith)
  have h := Real.one_sub_inv_le_log_of_pos hpos
  rw [inv_div, Real.log_div (by linarith) (by linarith)] at h
  have : 1 - (m - 1) / m = 1 / m := by field_simp; ring
  linarith

lemma sum_inv_le {n : ℕ} (hn : 2 ≤ n) :
    ∑ t ∈ Finset.range n, 1 / ((n : ℝ) + t) ≤ Real.log (2 * n - 1) - Real.log (n - 1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc ∑ t ∈ Finset.range n, 1 / ((n : ℝ) + t)
      ≤ ∑ t ∈ Finset.range n,
          (Real.log ((n : ℝ) - 1 + (t + 1 : ℕ)) - Real.log ((n : ℝ) - 1 + t)) := by
        refine Finset.sum_le_sum fun t _ => ?_
        have := inv_le_log_sub (m := (n : ℝ) + t) (by have : (0 : ℝ) ≤ t := t.cast_nonneg; linarith)
        have e1 : (n : ℝ) - 1 + ((t + 1 : ℕ) : ℝ) = n + t := by push_cast; ring
        have e2 : (n : ℝ) - 1 + t = (n + t) - 1 := by ring
        rw [e1, e2]; exact this
    _ = Real.log (2 * n - 1) - Real.log (n - 1) := by
        rw [Finset.sum_range_sub (fun t => Real.log ((n : ℝ) - 1 + t))]
        push_cast; ring_nf

lemma log_ratio_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log (2 * n - 1) - Real.log (n - 1) ≤ Real.log 2 + 1 / (2 * ((n : ℝ) - 1)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 0 < 1 / (2 * ((n : ℝ) - 1)) := by apply div_pos one_pos; linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have heq : (2 * (n : ℝ) - 1) = 2 * (1 + 1 / (2 * ((n : ℝ) - 1))) * (n - 1) := by
    field_simp; ring
  rw [heq, Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (by positivity)]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (2 * ((n : ℝ) - 1)) by positivity)
  linarith

/-- The lower bound `Λ₁ ≥ 1/log 2` [dBEr49, §3]. -/
theorem le_bigLambda_one : ENNReal.ofReal (1 / Real.log 2) ≤ bigLambda 1 := by
  refine le_iInf₂ fun a ha => ?_
  by_contra h
  have h : limsup (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * maxSpan a n 1)) atTop <
      ENNReal.ofReal (1 / Real.log 2) := not_le.mp h
  obtain ⟨c, hc1, hc2⟩ := exists_between h
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hc1 (by isBoundedDefault))
  have hct : c ≠ ⊤ := ne_top_of_lt hc2
  set c' := c.toReal
  have hc'0 : 0 ≤ c' := ENNReal.toReal_nonneg
  have hlog := log_two_pos'
  have hc'lt : c' * Real.log 2 < 1 := by
    have := ENNReal.toReal_lt_of_lt_ofReal hc2
    rw [lt_div_iff₀ hlog] at this; linarith
  have hbound : ∀ k ≥ max K 1, maxSpan a k 1 ≤ c' / k := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hM : 0 ≤ maxSpan a k 1 :=
      (div_nonneg zero_le_one hk0.le).trans (one_div_le_maxSpan (by omega))
    have := (ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg hk0.le hM) hct).mp
      (hK k (le_of_max_le_left hk))
    rw [le_div_iff₀ hk0]; linarith
  set δ := 1 - c' * Real.log 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (c' / (2 * δ))
  set n := max (max K 2) (N₁ + 1)
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
  have hnK : K ≤ n := le_trans (le_max_left _ _) (le_max_left _ _)
  have hnN : N₁ + 1 ≤ n := le_max_right _ _
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnN' : (N₁ : ℝ) + 1 ≤ n := by exact_mod_cast hnN
  have h1 := one_le_sum_maxSpan ha (n := n) (by omega)
  have h2 : ∑ t ∈ Finset.range n, maxSpan a (n + t) 1 ≤
      c' * ∑ t ∈ Finset.range n, 1 / ((n : ℝ) + t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    have := hbound (n + t) (by omega)
    push_cast at this
    rwa [mul_one_div]
  have h3 := mul_le_mul_of_nonneg_left ((sum_inv_le hn2).trans (log_ratio_le hn2)) hc'0
  -- `c' / (2 (n - 1)) < δ`
  have h4 : c' * (1 / (2 * ((n : ℝ) - 1))) < δ := by
    rw [mul_one_div, div_lt_iff₀ (by linarith)]
    rw [div_lt_iff₀ (by linarith)] at hN₁
    nlinarith
  simp only [δ] at h4
  nlinarith

/- ### The lower bound `λ₁ ≤ 1/log 4` -/

section SmallLambda

variable (ha : Function.Injective fun k ↦ Int.fract (a k))
include ha

/-- At time `N`, at most `2t` arcs are shorter than `m_{N-t}`: an arc whose endpoints both come
before time `N - t` was already an arc at time `N - t`. -/
lemma minSpan_le_gap_sort {N t s : ℕ} (hN : 2 ≤ N) (htN : t < N) (hs : 2 * t ≤ s) (hsN : s < N) :
    minSpan a (N - t) 1 ≤ gap a N (Tuple.sort (gap a N) ⟨s, hsN⟩) := by
  classical
  set τ := Tuple.sort (gap a N)
  have hmono : Monotone (gap a N ∘ τ) := Tuple.monotone_sort _
  set S : Finset (Fin N) := Finset.univ.image (fun s' : Fin (s + 1) => τ ⟨s', by omega⟩)
  have hS : S.card = s + 1 := by
    rw [Finset.card_image_of_injective _ (fun x y h => by
      have := congrArg Fin.val (τ.injective h); simp at this; exact Fin.ext this)]
    simp
  set B₁ : Finset (Fin N) := Finset.univ.filter (fun j => N - t ≤ (j : ℕ))
  set B₂ : Finset (Fin N) := Finset.univ.filter
    (fun j => ∃ h : (j : ℕ) < N - t, gap a N j < gap a (N - t) ⟨j, h⟩)
  have hB₁ : B₁.card ≤ t := by
    calc B₁.card ≤ (Finset.Ico (N - t) N).card :=
          Finset.card_le_card_of_injOn Fin.val
            (fun j hj => by simp [B₁] at hj; simp; omega)
            (fun x _ y _ h => Fin.ext h)
      _ = t := by simp; omega
  have hB₂ : B₂.card ≤ t := by
    have key : ∀ j ∈ B₂, ∃ m, N - t ≤ m ∧ m < N ∧ ∃ h : (j : ℕ) < N - t,
        Int.fract (a m - a j) < gap a (N - t) ⟨j, h⟩ := by
      intro j hj
      obtain ⟨h, hlt⟩ := (Finset.mem_filter.mp hj).2
      obtain ⟨j₁, q, hq, hidx, heq⟩ := exists_rSpan_eq_val ha hN (idx a N j)
      have hj₁ : j₁ = j := ((Tuple.sort (pts a N)).symm.injective hidx).symm
      rw [hj₁] at heq hq
      change gap a N j = _ at heq
      rcases Nat.lt_or_ge (q : ℕ) (N - t) with hqn | hqn
      · exfalso
        have := rSpan_le_val ha (n := N - t) (j₁ := ⟨j, h⟩) (j₂ := ⟨q, hqn⟩)
          (fun e => hq (Fin.ext (by simpa using congrArg Fin.val e)))
        change gap a (N - t) ⟨j, h⟩ ≤ _ at this
        simp only at this
        linarith
      · exact ⟨q, hqn, q.2, h, heq ▸ hlt⟩
    choose! f hf using key
    calc B₂.card ≤ (Finset.Ico (N - t) N).card := by
          refine Finset.card_le_card_of_injOn f (fun j hj => ?_) (fun j hj j' hj' hjj' => ?_)
          · obtain ⟨h1, h2, -⟩ := hf j hj; simp; omega
          · by_contra hne
            obtain ⟨-, -, h, h1⟩ := hf j hj
            obtain ⟨-, -, h', h2⟩ := hf j' hj'
            rw [hjj'] at h1
            exact arc_unique ha (n := N - t) (j := ⟨j, h⟩) (j' := ⟨j', h'⟩)
              (fun e => hne (Fin.ext (by simpa using congrArg Fin.val e))) _ h1 h2
      _ = t := by simp; omega
  obtain ⟨j, hj⟩ : (S \ (B₁ ∪ B₂)).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.le_card_sdiff (B₁ ∪ B₂) S
    have := Finset.card_union_le B₁ B₂
    omega
  obtain ⟨hjS, hjB⟩ := Finset.mem_sdiff.mp hj
  have hjt : (j : ℕ) < N - t := by
    by_contra h; exact hjB (Finset.mem_union_left _ (by simp [B₁]; omega))
  have hjg : gap a (N - t) ⟨j, hjt⟩ ≤ gap a N j := by
    by_contra h
    exact hjB (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjt,
      not_le.mp h⟩))
  obtain ⟨s', -, rfl⟩ := Finset.mem_image.mp hjS
  calc minSpan a (N - t) 1 ≤ gap a (N - t) ⟨_, hjt⟩ := minSpan_le_rSpan _
    _ ≤ gap a N (τ ⟨s', _⟩) := hjg
    _ ≤ gap a N (τ ⟨s, hsN⟩) := hmono (Fin.mk_le_mk.mpr (by omega))

omit ha in
lemma sum_range_two_mul (g : ℕ → ℝ) (n : ℕ) :
    ∑ s ∈ Finset.range (2 * n), g s = ∑ t ∈ Finset.range n, (g (2 * t) + g (2 * t + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

lemma two_mul_sum_minSpan_le {n : ℕ} (hn : 1 ≤ n) :
    2 * ∑ t ∈ Finset.range n, minSpan a (2 * n - t) 1 ≤ 1 := by
  set τ := Tuple.sort (gap a (2 * n))
  set f : ℕ → ℝ := fun s => if h : s < 2 * n then gap a (2 * n) (τ ⟨s, h⟩) else 0
  have h1 : (1 : ℝ) = ∑ s ∈ Finset.range (2 * n), f s := by
    rw [← sum_gap (a := a) (n := 2 * n) (by omega), ← Equiv.sum_comp τ (gap a (2 * n)),
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [f, s.2]
  rw [h1, sum_range_two_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun t ht => ?_
  rw [Finset.mem_range] at ht
  have e1 : f (2 * t) = gap a (2 * n) (τ ⟨2 * t, by omega⟩) := by simp [f, show 2 * t < 2 * n by omega]
  have e2 : f (2 * t + 1) = gap a (2 * n) (τ ⟨2 * t + 1, by omega⟩) := by
    simp [f, show 2 * t + 1 < 2 * n by omega]
  rw [e1, e2]
  have := minSpan_le_gap_sort ha (N := 2 * n) (t := t) (s := 2 * t) (by omega) (by omega) le_rfl
    (by omega)
  have := minSpan_le_gap_sort ha (N := 2 * n) (t := t) (s := 2 * t + 1) (by omega) (by omega)
    (by omega) (by omega)
  linarith

end SmallLambda

lemma log_sub_le_inv {m : ℝ} (hm : 0 < m) : Real.log (m + 1) - Real.log m ≤ 1 / m := by
  rw [← Real.log_div (by linarith) hm.ne']
  have := Real.log_le_sub_one_of_pos (show 0 < (m + 1) / m by positivity)
  rw [add_div, div_self hm.ne'] at this ⊢
  linarith

lemma log_sub_le_sum_inv (n : ℕ) :
    Real.log (2 * n + 1) - Real.log (n + 1) ≤ ∑ t ∈ Finset.range n, 1 / ((2 * n - t : ℕ) : ℝ) := by
  rw [← Finset.sum_range_reflect]
  calc Real.log (2 * n + 1) - Real.log (n + 1)
      = ∑ j ∈ Finset.range n,
          (Real.log ((n : ℝ) + 1 + (j + 1 : ℕ)) - Real.log ((n : ℝ) + 1 + j)) := by
        rw [Finset.sum_range_sub (fun j => Real.log ((n : ℝ) + 1 + j))]
        push_cast; ring_nf
    _ ≤ ∑ j ∈ Finset.range n, 1 / ((2 * n - (n - 1 - j) : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_range] at hj
        have e : ((2 * n - (n - 1 - j) : ℕ) : ℝ) = (n : ℝ) + 1 + j := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
          push_cast; ring
        rw [e]
        have := log_sub_le_inv (m := (n : ℝ) + 1 + j) (by positivity)
        push_cast
        rwa [show (n : ℝ) + 1 + (j + 1) = (n + 1 + j) + 1 by ring]

lemma log_two_sub_le {n : ℕ} :
    Real.log 2 - 1 / (2 * (n : ℝ) + 1) ≤ Real.log (2 * n + 1) - Real.log (n + 1) := by
  have hpos : (0 : ℝ) < (2 * n + 1) / (2 * n + 2) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hpos
  rw [inv_div, Real.log_div (by positivity) (by positivity)] at h
  have e : Real.log (2 * (n : ℝ) + 2) = Real.log 2 + Real.log (n + 1) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  have : 1 - (2 * (n : ℝ) + 2) / (2 * n + 1) = -(1 / (2 * n + 1)) := by
    field_simp; ring
  linarith

/-- The upper bound `λ₁ ≤ 1/log 4` [dBEr49, §4]. -/
theorem smallLambda_one_le : smallLambda 1 ≤ ENNReal.ofReal (1 / Real.log 4) := by
  refine iSup₂_le fun a ha => ?_
  by_contra h
  have h : ENNReal.ofReal (1 / Real.log 4) <
      liminf (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * minSpan a n 1)) atTop := not_le.mp h
  obtain ⟨c, hc1, hc2⟩ := exists_between h
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_lt_of_lt_liminf hc2 (by isBoundedDefault))
  have hct : c ≠ ⊤ := ne_top_of_lt hc2
  set c' := c.toReal
  have hlog := log_two_pos'
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hc'gt : 1 < 2 * c' * Real.log 2 := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hct).mp hc1
    rw [h4, div_lt_iff₀ (by positivity)] at this; linarith
  have hc'0 : 0 ≤ c' := ENNReal.toReal_nonneg
  have hbound : ∀ k ≥ max K 1, c' / k ≤ minSpan a k 1 := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have := ENNReal.toReal_lt_of_lt_ofReal (hK k (le_of_max_le_left hk))
    rw [div_le_iff₀ hk0]; linarith
  set δ := 2 * c' * Real.log 2 - 1
  have hδ : 0 < δ := by simp only [δ]; linarith
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 * c' / δ)
  set n := max (max K 1) N₁
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
  have hnK : K ≤ n := le_trans (le_max_left _ _) (le_max_left _ _)
  have hnN : N₁ ≤ n := le_max_right _ _
  have hnN' : (N₁ : ℝ) ≤ n := by exact_mod_cast hnN
  have h1 := two_mul_sum_minSpan_le ha hn1
  have h2 : c' * ∑ t ∈ Finset.range n, 1 / ((2 * n - t : ℕ) : ℝ) ≤
      ∑ t ∈ Finset.range n, minSpan a (2 * n - t) 1 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => ?_
    rw [Finset.mem_range] at ht
    have := hbound (2 * n - t) (by omega)
    rwa [mul_one_div]
  have h3 := mul_le_mul_of_nonneg_left
    ((log_two_sub_le (n := n)).trans (log_sub_le_sum_inv n)) hc'0
  -- `2 c' / (2n + 1) < δ`
  have h5 : 2 * c' * (1 / (2 * (n : ℝ) + 1)) < δ := by
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN₁
    nlinarith
  simp only [δ] at h5
  nlinarith

/-- **Erdős Problem 1221, case `r = 1`** [dBEr49, §§2–5]:
`Λ₁ = 1/log 2`, `λ₁ = 1/log 4` and `μ₁ = 2`. The type is that of
`Erdos1221.erdos_1221.variants.r_one` in formal-conjectures. -/
theorem erdos_1221_r_one :
    bigLambda 1 = ENNReal.ofReal (1 / Real.log 2) ∧
      smallLambda 1 = ENNReal.ofReal (1 / Real.log 4) ∧ mu 1 = 2 :=
  ⟨le_antisymm bigLambda_one_le le_bigLambda_one,
    le_antisymm smallLambda_one_le le_smallLambda_one,
    le_antisymm mu_one_le two_le_mu_one⟩

end Erdos1221.ROne


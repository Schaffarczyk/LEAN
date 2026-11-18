/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Existence and uniqueness for Blasius's boundary-layer problem

A formalisation of §2 of

  H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
  Annals of Mathematics 43 (1942), 381–407.

Weyl's problem `(A₀)` asks for a function `w` on `[0, ∞)` with

  `w''' + 2 w w'' = 0`,   `w(0) = w'(0) = 0`,   `w'(z) → k`  as `z → ∞`.

Following Weyl (and Töpfer), we first construct the solution `f` with
`f(0) = f'(0) = 0`, `f''(0) = 1`.  Writing `g = f''`, the initial value problem is
equivalent to the integral equation

  `g = Φ{g}`,   `Φ{g}(z) = exp (-∫₀ᶻ (z - ζ)² g(ζ) dζ)`            (Weyl's (12)).

Since `∫₀ᶻ (z - ζ)² g(ζ) dζ` is twice the threefold iterated primitive of `g`, we write
`Φ{g} = exp (-2 J³ g)` with `J g (z) = ∫₀ᶻ g`.  The successive approximations
`g₀ = 0`, `gₙ₊₁ = Φ{gₙ}` satisfy Weyl's estimate (16),

  `|gₙ₊₁(z) - gₙ(z)| ≤ (2 z³)ⁿ / (3n)!`,

hence converge; the limit solves the integral equation.  Finally `f' = J g` is increasing
and bounded, so it has a positive limit `β`, and `w(z) = κ f(κ z)` with `κ² β = k`
solves `(A₀)`.

Uniqueness is proved as well: for the initial-value problem by applying the estimate (16) to
the difference of two solutions, for the boundary-value problem by Töpfer's scaling.

Main results: `Blasius.weyl_A0_exists`, `Blasius.weyl_A0_unique`, `Blasius.blasius_exists`,
`Blasius.blasius_exists_deriv`, `Blasius.exists_isBlasiusSol`, `Blasius.IsBlasiusSol.unique`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Set Filter Topology MeasureTheory
open scoped Nat

noncomputable section

namespace Blasius

/-- `deriv_conv h` closes a goal `HasDerivAt f f' x` (or `HasDerivWithinAt f f' s x`) from
`h : HasDerivAt f g' x`, leaving the goal `f' = g'`. -/
macro "deriv_conv " h:term : tactic =>
  `(tactic| (first
    | refine HasDerivAt.congr_deriv $h (Eq.symm ?_)
    | refine HasDerivWithinAt.congr_deriv $h (Eq.symm ?_)) <;> beta_reduce)

/-! ## The primitive `J g (z) = ∫₀ᶻ g` -/

/-- The primitive of `g` vanishing at `0`. -/
def J (g : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in (0 : ℝ)..z, g t

@[simp] lemma J_apply_zero (g : ℝ → ℝ) : J g 0 = 0 := by simp [J]

lemma J_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (z : ℝ) : HasDerivAt (J g) (g z) z :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt

lemma J_continuous {g : ℝ → ℝ} (hg : Continuous g) : Continuous (J g) :=
  continuous_iff_continuousAt.2 fun z => (J_hasDerivAt hg z).continuousAt

lemma J_nonneg {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ t → 0 ≤ g t) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ J g z :=
  intervalIntegral.integral_nonneg hz fun t ht => hg t ht.1

lemma J_sub_le {u v d : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) (hd : Continuous d)
    (h : ∀ t, 0 ≤ t → |u t - v t| ≤ d t) {z : ℝ} (hz : 0 ≤ z) :
    |J u z - J v z| ≤ J d z := by
  unfold J
  rw [← intervalIntegral.integral_sub (hu.intervalIntegrable _ _) (hv.intervalIntegrable _ _)]
  calc |∫ t in (0 : ℝ)..z, (u t - v t)| ≤ ∫ t in (0 : ℝ)..z, |u t - v t| :=
        intervalIntegral.abs_integral_le_integral_abs hz
    _ ≤ ∫ t in (0 : ℝ)..z, d t :=
        intervalIntegral.integral_mono_on hz ((hu.sub hv).abs.intervalIntegrable _ _)
          (hd.intervalIntegrable _ _) fun t ht => h t ht.1

lemma J_abs_le {F B : ℝ → ℝ} (hB : Continuous B) (hb : ∀ x, |F x| ≤ B x) (z : ℝ) :
    |J F z| ≤ |J B z| := by
  have := intervalIntegral.norm_integral_le_abs_of_norm_le (f := F) (g := B) (a := 0) (b := z)
    (μ := volume) (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
    (hB.intervalIntegrable _ _)
  simpa [J, Real.norm_eq_abs] using this

/-- Dominated convergence for the primitive. -/
lemma J_tendsto {F : ℕ → ℝ → ℝ} {f B : ℝ → ℝ} (hF : ∀ n, Continuous (F n)) (hB : Continuous B)
    (hb : ∀ n x, |F n x| ≤ B x) (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (z : ℝ) : Tendsto (fun n => J (F n) z) atTop (𝓝 (J f z)) := by
  unfold J
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence B
    (Eventually.of_forall fun n => (hF n).aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall fun x _ => by
      rw [Real.norm_eq_abs]; exact hb n x)
    (hB.intervalIntegrable _ _)
    (Eventually.of_forall fun x _ => hlim x)

lemma J_monomial (c : ℝ) (k : ℕ) (z : ℝ) :
    J (fun t => c * t ^ k) z = c / (k + 1) * z ^ (k + 1) := by
  unfold J
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have h : ∀ t ∈ Set.uIcc (0 : ℝ) z,
      HasDerivAt (fun t : ℝ => c / (k + 1) * t ^ (k + 1)) (c * t ^ k) t := by
    intro t _
    have := (hasDerivAt_pow (k + 1) t).const_mul (c / ((k : ℝ) + 1))
    deriv_conv this
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((by fun_prop : Continuous fun t : ℝ => c * t ^ k).intervalIntegrable _ _)]
  simp

lemma J_monomial' (c : ℝ) (k : ℕ) :
    J (fun t => c * t ^ k) = fun z => c / (k + 1) * z ^ (k + 1) :=
  funext (J_monomial c k)

/-! ## The operator `Φ{g} = exp (-2 J³ g)` -/

/-- Threefold primitive; `2 * K g z = ∫₀ᶻ (z - ζ)² g(ζ) dζ` is Weyl's `G(z)`, eq. (15). -/
def K (g : ℝ → ℝ) : ℝ → ℝ := J (J (J g))

@[simp] lemma K_apply_zero (g : ℝ → ℝ) : K g 0 = 0 := by simp [K]

lemma K_continuous {g : ℝ → ℝ} (hg : Continuous g) : Continuous (K g) :=
  J_continuous (J_continuous (J_continuous hg))

lemma K_nonneg {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ t → 0 ≤ g t) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ K g z :=
  J_nonneg (fun _ ht => J_nonneg (fun _ hs => J_nonneg hg hs) ht) hz

lemma K_sub_le {u v d : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) (hd : Continuous d)
    (h : ∀ t, 0 ≤ t → |u t - v t| ≤ d t) {z : ℝ} (hz : 0 ≤ z) :
    |K u z - K v z| ≤ K d z :=
  J_sub_le (J_continuous (J_continuous hu)) (J_continuous (J_continuous hv))
    (J_continuous (J_continuous hd))
    (fun _ ht => J_sub_le (J_continuous hu) (J_continuous hv) (J_continuous hd)
      (fun _ hs => J_sub_le hu hv hd h hs) ht) hz

lemma K_monomial (c : ℝ) (k : ℕ) (z : ℝ) :
    K (fun t => c * t ^ k) z = c / ((k + 1) * (k + 2) * (k + 3)) * z ^ (k + 3) := by
  unfold K
  rw [J_monomial', J_monomial', J_monomial]
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (k : ℝ) + 3 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Weyl's operator `Φ` of eq. (12).  The argument is clamped at `0` so that `Φ g` is defined
and continuous on all of `ℝ`; only its values on `[0, ∞)` matter. -/
def Φ (g : ℝ → ℝ) (z : ℝ) : ℝ := Real.exp (-(2 * K g (max z 0)))

lemma Φ_continuous {g : ℝ → ℝ} (hg : Continuous g) : Continuous (Φ g) := by
  have hK := K_continuous hg
  unfold Φ
  fun_prop

lemma Φ_pos (g : ℝ → ℝ) (z : ℝ) : 0 < Φ g z := Real.exp_pos _

lemma Φ_le_one {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ t → 0 ≤ g t) (z : ℝ) : Φ g z ≤ 1 := by
  unfold Φ
  rw [Real.exp_le_one_iff]
  have := K_nonneg hg (le_max_right z 0)
  linarith

lemma Φ_max (g : ℝ → ℝ) (z : ℝ) : Φ g (max z 0) = Φ g z := by
  unfold Φ
  rw [max_eq_left (le_max_right z 0)]

/-- `0 ≤ e⁻ᵘ - e⁻ᵛ ≤ v - u` for `0 ≤ u ≤ v` (Weyl, p. 387), in symmetric form. -/
lemma abs_exp_neg_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  wlog h : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact this hb ha (le_of_not_ge h)
  have hE : 0 < Real.exp (-a) := Real.exp_pos _
  have hE1 : Real.exp (-a) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hX : -(b - a) + 1 ≤ Real.exp (-(b - a)) := Real.add_one_le_exp _
  have hmul : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hle : Real.exp (-b) ≤ Real.exp (-a) := by rw [Real.exp_le_exp]; linarith
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), hmul]
  nlinarith [mul_le_mul_of_nonneg_left hX hE.le,
    mul_le_mul_of_nonneg_right hE1 (sub_nonneg.2 h)]

/-! ## Successive approximations -/

/-- Weyl's successive approximations `g₀ = 0`, `gₙ₊₁ = Φ{gₙ}`. -/
def gseq : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => Φ (gseq n)

lemma gseq_continuous : ∀ n, Continuous (gseq n)
  | 0 => continuous_const
  | n + 1 => Φ_continuous (gseq_continuous n)

lemma gseq_nonneg (n : ℕ) (z : ℝ) : 0 ≤ gseq n z := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact (Φ_pos _ _).le

lemma gseq_le_one (n : ℕ) (z : ℝ) : gseq n z ≤ 1 := by
  cases n with
  | zero => exact zero_le_one
  | succ n => exact Φ_le_one (fun t _ => gseq_nonneg n t) z

/-- Coefficients of the majorants: `|gₙ₊₁(z) - gₙ(z)| ≤ a n * z ^ (3 n)`.
In closed form `a n = 2ⁿ / (3n)!`, cf. Weyl's (16). -/
def a : ℕ → ℝ
  | 0 => 1
  | n + 1 => 2 * a n / ((3 * n + 1) * (3 * n + 2) * (3 * n + 3))

lemma a_nonneg : ∀ n, 0 ≤ a n
  | 0 => zero_le_one
  | n + 1 => by
      have := a_nonneg n
      rw [a]
      positivity

lemma a_le : ∀ n : ℕ, a n ≤ 2 ^ n / n !
  | 0 => by simp [a]
  | n + 1 => by
      have ih := a_le n
      have h0 := a_nonneg n
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hD : (n : ℝ) + 1 ≤ (3 * n + 1) * (3 * n + 2) * (3 * n + 3) := by
        have : (1 : ℝ) ≤ (3 * n + 1) * (3 * n + 2) := by nlinarith
        nlinarith
      have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
      rw [a]
      calc 2 * a n / ((3 * n + 1) * (3 * n + 2) * (3 * n + 3))
          ≤ 2 * a n / (n + 1) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hD
        _ ≤ 2 * (2 ^ n / n !) / (n + 1) := by gcongr
        _ = 2 ^ (n + 1) / (n + 1)! := by
            rw [Nat.factorial_succ]
            push_cast
            field_simp
            ring

/-- Weyl's estimate (16) on `[0, ∞)`. -/
lemma gseq_diff_nonneg : ∀ (n : ℕ) (z : ℝ), 0 ≤ z →
    |gseq (n + 1) z - gseq n z| ≤ a n * z ^ (3 * n)
  | 0, z, _ => by
      have h1 := gseq_nonneg 1 z
      have h2 := gseq_le_one 1 z
      have h0 : gseq 0 z = 0 := rfl
      rw [h0, sub_zero, abs_of_nonneg h1]
      simpa [a] using h2
  | n + 1, z, hz => by
      have ih := gseq_diff_nonneg n
      have hK := K_sub_le (gseq_continuous (n + 1)) (gseq_continuous n)
        (d := fun t => a n * t ^ (3 * n)) (by fun_prop) ih hz
      rw [K_monomial] at hK
      push_cast at hK
      have hmax : max z 0 = z := max_eq_left hz
      have hp : 0 ≤ K (gseq (n + 1)) z := K_nonneg (fun t _ => gseq_nonneg _ t) hz
      have hq : 0 ≤ K (gseq n) z := K_nonneg (fun t _ => gseq_nonneg _ t) hz
      show |Φ (gseq (n + 1)) z - Φ (gseq n) z| ≤ _
      unfold Φ
      rw [hmax]
      calc |Real.exp (-(2 * K (gseq (n + 1)) z)) - Real.exp (-(2 * K (gseq n) z))|
          ≤ |2 * K (gseq (n + 1)) z - 2 * K (gseq n) z| :=
            abs_exp_neg_sub_le (by positivity) (by positivity)
        _ = 2 * |K (gseq (n + 1)) z - K (gseq n) z| := by
            rw [← mul_sub, abs_mul, abs_two]
        _ ≤ 2 * (a n / ((3 * n + 1) * (3 * n + 2) * (3 * n + 3)) * z ^ (3 * n + 3)) :=
            mul_le_mul_of_nonneg_left hK zero_le_two
        _ = a (n + 1) * z ^ (3 * (n + 1)) := by
            rw [a]
            ring

/-- Weyl's estimate (16), for all real `z` (both sides only depend on `max z 0`). -/
lemma gseq_diff (n : ℕ) (z : ℝ) :
    |gseq (n + 1) z - gseq n z| ≤ a n * (max z 0) ^ (3 * n) := by
  cases n with
  | zero =>
    have h1 := gseq_nonneg 1 z
    have h2 := gseq_le_one 1 z
    have h0 : gseq 0 z = 0 := rfl
    rw [h0, sub_zero, abs_of_nonneg h1]
    simpa [a] using h2
  | succ n =>
    have e1 : gseq (n + 1 + 1) z = gseq (n + 1 + 1) (max z 0) := (Φ_max _ z).symm
    have e2 : gseq (n + 1) z = gseq (n + 1) (max z 0) := (Φ_max _ z).symm
    rw [e1, e2]
    exact gseq_diff_nonneg (n + 1) _ (le_max_right z 0)

lemma gseq_cauchy (z : ℝ) : CauchySeq (fun n => gseq n z) := by
  have hm : 0 ≤ max z 0 := le_max_right _ _
  refine cauchySeq_of_dist_le_of_summable (fun n => (2 * (max z 0) ^ 3) ^ n / n !)
    (fun n => ?_) (Real.summable_pow_div_factorial _)
  rw [Real.dist_eq, abs_sub_comm]
  calc |gseq (n + 1) z - gseq n z| ≤ a n * (max z 0) ^ (3 * n) := gseq_diff n z
    _ ≤ 2 ^ n / n ! * (max z 0) ^ (3 * n) :=
        mul_le_mul_of_nonneg_right (a_le n) (by positivity)
    _ = (2 * (max z 0) ^ 3) ^ n / n ! := by
        rw [mul_pow, ← pow_mul]
        ring

/-! ## The limit function `g = f''` -/

/-- The limit of the successive approximations; it is `f''` for Töpfer's solution `f`. -/
def g (z : ℝ) : ℝ := limUnder atTop (fun n => gseq n z)

lemma gseq_tendsto (z : ℝ) : Tendsto (fun n => gseq n z) atTop (𝓝 (g z)) :=
  (gseq_cauchy z).tendsto_limUnder

lemma g_nonneg (z : ℝ) : 0 ≤ g z :=
  ge_of_tendsto' (gseq_tendsto z) fun n => gseq_nonneg n z

lemma g_le_one (z : ℝ) : g z ≤ 1 :=
  le_of_tendsto' (gseq_tendsto z) fun n => gseq_le_one n z

lemma K_tendsto (z : ℝ) : Tendsto (fun n => K (gseq n) z) atTop (𝓝 (K g z)) := by
  have c0 : Continuous (fun _ : ℝ => (1 : ℝ)) := continuous_const
  have c1 : Continuous (fun x => |J (fun _ : ℝ => (1 : ℝ)) x|) := (J_continuous c0).abs
  have c2 : Continuous (fun y => |J (fun x => |J (fun _ : ℝ => (1 : ℝ)) x|) y|) :=
    (J_continuous c1).abs
  have b0 : ∀ n x, |gseq n x| ≤ 1 := fun n x =>
    abs_le.2 ⟨by linarith [gseq_nonneg n x], gseq_le_one n x⟩
  have b1 : ∀ n x, |J (gseq n) x| ≤ |J (fun _ : ℝ => (1 : ℝ)) x| := fun n x =>
    J_abs_le c0 (b0 n) x
  have b2 : ∀ n x, |J (J (gseq n)) x| ≤ |J (fun x => |J (fun _ : ℝ => (1 : ℝ)) x|) x| :=
    fun n x => J_abs_le c1 (b1 n) x
  have t1 := J_tendsto (fun n => gseq_continuous n) c0 b0 gseq_tendsto
  have t2 := J_tendsto (fun n => J_continuous (gseq_continuous n)) c1 b1 t1
  exact J_tendsto (fun n => J_continuous (J_continuous (gseq_continuous n))) c2 b2 t2 z

/-- The limit solves Weyl's integral equation (12), `g = Φ{g}`. -/
lemma g_fix (z : ℝ) : g z = Real.exp (-(2 * K g (max z 0))) := by
  have h1 : Tendsto (fun n => gseq (n + 1) z) atTop (𝓝 (g z)) :=
    (gseq_tendsto z).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => gseq (n + 1) z) atTop (𝓝 (Real.exp (-(2 * K g (max z 0))))) :=
    (Real.continuous_exp.tendsto _).comp (((K_tendsto (max z 0)).const_mul 2).neg)
  exact tendsto_nhds_unique h1 h2

lemma g_pos (z : ℝ) : 0 < g z := by
  rw [g_fix]
  exact Real.exp_pos _

lemma g_measurable : Measurable g :=
  measurable_of_tendsto_metrizable (fun n => (gseq_continuous n).measurable)
    (tendsto_pi_nhds.2 gseq_tendsto)

lemma g_intervalIntegrable (a b : ℝ) : IntervalIntegrable g volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    g_measurable.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  show ‖g x‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (g_nonneg x)]
  exact g_le_one x

lemma g_continuous : Continuous g := by
  have hJ : Continuous (J g) := intervalIntegral.continuous_primitive g_intervalIntegrable 0
  have hK : Continuous (K g) := J_continuous (J_continuous hJ)
  have h : g = fun z => Real.exp (-(2 * K g (max z 0))) := funext g_fix
  rw [h]
  fun_prop

/-! ## Töpfer's solution: `f(0) = f'(0) = 0`, `f''(0) = 1` -/

/-- `f' = J g`. -/
def f1 : ℝ → ℝ := J g

/-- Töpfer's solution `f = J (J g)`. -/
def f0 : ℝ → ℝ := J f1

/-- A globally differentiable function agreeing with `g = f''` on `[0, ∞)`. -/
def h (z : ℝ) : ℝ := Real.exp (-(2 * J f0 z))

lemma f1_continuous : Continuous f1 := J_continuous g_continuous

lemma f0_continuous : Continuous f0 := J_continuous f1_continuous

lemma hasDerivAt_f0 (z : ℝ) : HasDerivAt f0 (f1 z) z := J_hasDerivAt f1_continuous z

lemma hasDerivAt_f1 (z : ℝ) : HasDerivAt f1 (g z) z := J_hasDerivAt g_continuous z

lemma hasDerivAt_h (z : ℝ) : HasDerivAt h (-(2 * f0 z * h z)) z := by
  have hJ : HasDerivAt (J f0) (f0 z) z := J_hasDerivAt f0_continuous z
  have h2 : HasDerivAt (fun x => -(2 * J f0 x)) (-(2 * f0 z)) z := (hJ.const_mul 2).neg
  have h3 := h2.exp
  deriv_conv h3
  unfold h
  ring

lemma g_eq_h {z : ℝ} (hz : 0 ≤ z) : g z = h z := by
  rw [g_fix z, max_eq_left hz]
  rfl

@[simp] lemma f0_zero : f0 0 = 0 := J_apply_zero _

@[simp] lemma f1_zero : f1 0 = 0 := J_apply_zero _

lemma g_zero : g 0 = 1 := by
  rw [g_fix 0]
  simp

/-- The differential equation `f''' = -2 f f''` on `[0, ∞)` (one-sided at `0`). -/
lemma hasDerivWithinAt_g {z : ℝ} (hz : 0 ≤ z) :
    HasDerivWithinAt g (-(2 * f0 z * g z)) (Ici 0) z := by
  have h1 : HasDerivWithinAt h (-(2 * f0 z * h z)) (Ici 0) z := (hasDerivAt_h z).hasDerivWithinAt
  rw [← g_eq_h hz] at h1
  exact h1.congr (fun x hx => g_eq_h hx) (g_eq_h hz)

lemma hasDerivAt_g {z : ℝ} (hz : 0 < z) : HasDerivAt g (-(2 * f0 z * g z)) z :=
  (hasDerivWithinAt_g hz.le).hasDerivAt (Ici_mem_nhds hz)

/-! ## Asymptotic behaviour: `f'` has a finite positive limit -/

lemma f1_mono : Monotone f1 :=
  monotone_of_deriv_nonneg (fun z => (hasDerivAt_f1 z).differentiableAt) fun z => by
    rw [(hasDerivAt_f1 z).deriv]
    exact g_nonneg z

lemma f1_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ f1 z := by
  simpa using f1_mono hz

lemma f1_pos {z : ℝ} (hz : 0 < z) : 0 < f1 z :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (g_continuous.intervalIntegrable _ _)
    (fun x _ => g_pos x) hz

lemma f0_pos {z : ℝ} (hz : 0 < z) : 0 < f0 z :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (f1_continuous.intervalIntegrable _ _)
    (fun _ hx => f1_pos hx.1) hz

lemma f0_monoOn : MonotoneOn f0 (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) f0_continuous.continuousOn
    (fun x _ => (hasDerivAt_f0 x).differentiableAt.differentiableWithinAt) fun x hx => ?_
  rw [interior_Ici] at hx
  rw [(hasDerivAt_f0 x).deriv]
  exact f1_nonneg (le_of_lt hx)

/-- `f'` is bounded: with `c = f(1) > 0`, the function `f'' + 2 c f'` is non-increasing on
`[1, ∞)` because `f''' = -2 f f'' ≤ -2 c f''` there.  (Weyl obtains the sharper Gaussian bound
`g(z) ≤ exp (-c (z - z₀)²)`; boundedness of `f'` is all we need.) -/
lemma f1_bddAbove : BddAbove (range f1) := by
  set c := f0 1 with hc
  have hcpos : 0 < c := f0_pos one_pos
  have hanti : AntitoneOn (fun z => g z + 2 * c * f1 z) (Ici 1) := by
    have hd : ∀ x, 1 < x →
        HasDerivAt (fun z => g z + 2 * c * f1 z) (-(2 * f0 x * g x) + 2 * c * g x) x :=
      fun x hx => (hasDerivAt_g (by linarith)).add ((hasDerivAt_f1 x).const_mul (2 * c))
    refine antitoneOn_of_deriv_nonpos (convex_Ici 1)
      (g_continuous.add (continuous_const.mul f1_continuous)).continuousOn
      (fun x hx => ?_) fun x hx => ?_
    · rw [interior_Ici] at hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ici] at hx
      rw [(hd x hx).deriv]
      have hfc : c ≤ f0 x := f0_monoOn (mem_Ici.2 zero_le_one)
        (mem_Ici.2 (zero_le_one.trans (le_of_lt hx))) (le_of_lt hx)
      nlinarith [mul_nonneg (g_nonneg x) (sub_nonneg.2 hfc)]
  refine ⟨(g 1 + 2 * c * f1 1) / (2 * c), ?_⟩
  rintro _ ⟨z, rfl⟩
  rw [le_div_iff₀ (by positivity)]
  rcases le_total z 1 with hz | hz
  · have := f1_mono hz
    nlinarith [g_nonneg 1]
  · have := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hz) hz
    simp only at this
    linarith [g_nonneg z]

/-- Weyl's constant `β = ∫₀^∞ f''(z) dz = lim f'(z)`. -/
def β : ℝ := ⨆ z, f1 z

lemma f1_tendsto : Tendsto f1 atTop (𝓝 β) := tendsto_atTop_ciSup f1_mono f1_bddAbove

lemma β_pos : 0 < β := lt_of_lt_of_le (f1_pos one_pos) (le_ciSup f1_bddAbove 1)

/-! ## Main theorems -/

/-- **Weyl (1942), problem `(A₀)`.**  For every `k > 0` there is a function `w` with
`w''' + 2 w w'' = 0` on `[0, ∞)`, `w(0) = w'(0) = 0` and `w'(z) → k` as `z → ∞`.
Here `w₁ = w'` and `w₂ = w''`; the third derivative is one-sided at `z = 0`. -/
theorem weyl_A0_exists (k : ℝ) (hk : 0 < k) :
    ∃ w w₁ w₂ : ℝ → ℝ,
      (∀ z, HasDerivAt w (w₁ z) z) ∧
      (∀ z, HasDerivAt w₁ (w₂ z) z) ∧
      (∀ z, 0 ≤ z → HasDerivWithinAt w₂ (-(2 * w z * w₂ z)) (Ici 0) z) ∧
      w 0 = 0 ∧ w₁ 0 = 0 ∧ Tendsto w₁ atTop (𝓝 k) := by
  set κ := Real.sqrt (k / β) with hκdef
  have hκ : 0 < κ := Real.sqrt_pos.2 (div_pos hk β_pos)
  have hκ2 : κ ^ 2 * β = k := by
    rw [hκdef, Real.sq_sqrt (div_pos hk β_pos).le, div_mul_cancel₀ _ β_pos.ne']
  have hlin : ∀ z : ℝ, HasDerivAt (fun z => κ * z) κ z := fun z => by
    simpa using (hasDerivAt_id z).const_mul κ
  refine ⟨fun z => κ * f0 (κ * z), fun z => κ ^ 2 * f1 (κ * z), fun z => κ ^ 3 * g (κ * z),
    fun z => ?_, fun z => ?_, fun z hz => ?_, by simp, by simp, ?_⟩
  · have := ((hasDerivAt_f0 (κ * z)).comp z (hlin z)).const_mul κ
    deriv_conv this
    ring
  · have := ((hasDerivAt_f1 (κ * z)).comp z (hlin z)).const_mul (κ ^ 2)
    deriv_conv this
    ring
  · have hmaps : MapsTo (fun z => κ * z) (Ici (0 : ℝ)) (Ici 0) := fun x hx =>
      mul_nonneg hκ.le hx
    have := ((hasDerivWithinAt_g (mul_nonneg hκ.le hz)).comp z
      (hlin z).hasDerivWithinAt hmaps).const_mul (κ ^ 3)
    deriv_conv this
    ring
  · have h1 : Tendsto (fun z => κ * z) atTop atTop := tendsto_id.const_mul_atTop hκ
    have h2 := (f1_tendsto.comp h1).const_mul (κ ^ 2)
    rw [hκ2] at h2
    exact h2

/-- **Existence for Blasius's problem** in its classical normalisation:
`f''' + f f'' = 0` on `[0, ∞)`, `f(0) = f'(0) = 0`, `f'(η) → 1` as `η → ∞`.
Here `f₁ = f'`, `f₂ = f''`; the third derivative is one-sided at `η = 0`. -/
theorem blasius_exists :
    ∃ f f₁ f₂ : ℝ → ℝ,
      (∀ η, HasDerivAt f (f₁ η) η) ∧
      (∀ η, HasDerivAt f₁ (f₂ η) η) ∧
      (∀ η, 0 ≤ η → HasDerivWithinAt f₂ (-(f η * f₂ η)) (Ici 0) η) ∧
      f 0 = 0 ∧ f₁ 0 = 0 ∧ Tendsto f₁ atTop (𝓝 1) := by
  obtain ⟨w, w₁, w₂, h0, h1, h2, hw0, hw1, hlim⟩ := weyl_A0_exists (1 / 2) (by norm_num)
  refine ⟨fun z => 2 * w z, fun z => 2 * w₁ z, fun z => 2 * w₂ z,
    fun z => (h0 z).const_mul 2, fun z => (h1 z).const_mul 2, fun z hz => ?_,
    by simp [hw0], by simp [hw1], ?_⟩
  · have := (h2 z hz).const_mul 2
    deriv_conv this
    ring
  · have := hlim.const_mul 2
    norm_num at this
    exact this

/-- Blasius's problem stated with `deriv`: there is a twice differentiable `f : ℝ → ℝ`
whose second derivative is differentiable on `(0, ∞)`, with
`f''' + f f'' = 0` on `(0, ∞)`, `f(0) = f'(0) = 0` and `f'(η) → 1` as `η → ∞`. -/
theorem blasius_exists_deriv :
    ∃ f : ℝ → ℝ,
      Differentiable ℝ f ∧ Differentiable ℝ (deriv f) ∧
      (∀ η, 0 < η → DifferentiableAt ℝ (deriv (deriv f)) η) ∧
      (∀ η, 0 < η → deriv (deriv (deriv f)) η + f η * deriv (deriv f) η = 0) ∧
      f 0 = 0 ∧ deriv f 0 = 0 ∧ Tendsto (deriv f) atTop (𝓝 1) := by
  obtain ⟨f, f₁, f₂, h0, h1, h2, hf0, hf1, hlim⟩ := blasius_exists
  have e1 : deriv f = f₁ := funext fun z => (h0 z).deriv
  have e2 : deriv f₁ = f₂ := funext fun z => (h1 z).deriv
  have h3 : ∀ η, 0 < η → HasDerivAt f₂ (-(f η * f₂ η)) η := fun η hη =>
    (h2 η hη.le).hasDerivAt (Ici_mem_nhds hη)
  refine ⟨f, fun z => (h0 z).differentiableAt, ?_, ?_, ?_, hf0, ?_, ?_⟩
  · rw [e1]
    exact fun z => (h1 z).differentiableAt
  · intro η hη
    rw [e1, e2]
    exact (h3 η hη).differentiableAt
  · intro η hη
    rw [e1, e2, (h3 η hη).deriv]
    ring
  · rw [e1]
    exact hf1
  · rw [e1]
    exact hlim

/-! ## Uniqueness

We work with triples `(w, w₁, w₂)` of functions, where `w₁ = w'`, `w₂ = w''` on `[0, ∞)` in
the sense of one-sided-at-`0` derivatives (`HasDerivWithinAt … (Ici 0)`); nothing is assumed
about the values on `(-∞, 0)`.

* `IsSol.rep`: every solution satisfies `w''(z) = w''(0) · exp (-2 J³ w''(z))`.
* `fix_unique`: this integral equation has at most one continuous solution for given
  `σ = w''(0) > 0` (Weyl's estimate (16) applied to the difference of two solutions).
* `IsSol.pos_of_tendsto`: `w'(z) → k > 0` forces `w''(0) > 0`.
* `weyl_A0_unique`: Töpfer's scaling `w ↦ κ w(κ ·)` reduces the boundary-value problem to
  the initial-value problem; the limit `k` then fixes `κ = 1`.
-/

/-- `(w, w₁, w₂)` solves `w''' + 2 w w'' = 0` on `[0, ∞)` with `w(0) = w'(0) = 0`. -/
structure IsSol (w w₁ w₂ : ℝ → ℝ) : Prop where
  d0 : ∀ z, 0 ≤ z → HasDerivWithinAt w (w₁ z) (Ici 0) z
  d1 : ∀ z, 0 ≤ z → HasDerivWithinAt w₁ (w₂ z) (Ici 0) z
  d2 : ∀ z, 0 ≤ z → HasDerivWithinAt w₂ (-(2 * w z * w₂ z)) (Ici 0) z
  z0 : w 0 = 0
  z1 : w₁ 0 = 0

/-- Extension of `F|[0,∞)` to `ℝ` by the constant `F 0`. -/
def clamp (F : ℝ → ℝ) (z : ℝ) : ℝ := F (max z 0)

lemma clamp_of_nonneg (F : ℝ → ℝ) {z : ℝ} (hz : 0 ≤ z) : clamp F z = F z := by
  simp [clamp, max_eq_left hz]

lemma continuous_clamp {F : ℝ → ℝ} (hF : ContinuousOn F (Ici 0)) : Continuous (clamp F) :=
  hF.comp_continuous (continuous_id.max continuous_const) fun z => le_max_right z 0

lemma J_congr {p ψ : ℝ → ℝ} (h : ∀ t, 0 ≤ t → p t = ψ t) {z : ℝ} (hz : 0 ≤ z) :
    J p z = J ψ z :=
  intervalIntegral.integral_congr fun t ht => h t (by rw [uIcc_of_le hz] at ht; exact ht.1)

/-- A function with right derivative `p` on `[0, ∞)` vanishing at `0` is the primitive of `p`. -/
lemma eq_J_of_hasDerivWithinAt {F p : ℝ → ℝ} (hp : Continuous p)
    (hF : ∀ z, 0 ≤ z → HasDerivWithinAt F (p z) (Ici 0) z) (h0 : F 0 = 0) {z : ℝ}
    (hz : 0 ≤ z) : F z = J p z := by
  have hFc : ContinuousOn F (Ici 0) := fun x hx => (hF x hx).continuousWithinAt
  have hc : ContinuousOn (fun x => F x - J p x) (Icc 0 z) :=
    (hFc.mono Icc_subset_Ici_self).sub (J_continuous hp).continuousOn
  have hd : ∀ x ∈ Ico 0 z, HasDerivWithinAt (fun x => F x - J p x) 0 (Ici x) x := by
    intro x hx
    have := ((hF x hx.1).mono (Ici_subset_Ici.2 hx.1)).sub
      (J_hasDerivAt hp x).hasDerivWithinAt
    exact this.congr_deriv (sub_self _)
  have key : F z - J p z = F 0 - J p 0 :=
    constant_of_has_deriv_right_zero hc hd z (right_mem_Icc.2 hz)
  rw [h0, J_apply_zero] at key
  linarith

namespace IsSol

variable {w w₁ w₂ : ℝ → ℝ}

lemma cont2 (h : IsSol w w₁ w₂) : Continuous (clamp w₂) :=
  continuous_clamp fun z hz => (h.d2 z hz).continuousWithinAt

lemma w1_eq (h : IsSol w w₁ w₂) {z : ℝ} (hz : 0 ≤ z) : w₁ z = J (clamp w₂) z :=
  eq_J_of_hasDerivWithinAt h.cont2
    (fun x hx => by rw [clamp_of_nonneg _ hx]; exact h.d1 x hx) h.z1 hz

lemma w_eq (h : IsSol w w₁ w₂) {z : ℝ} (hz : 0 ≤ z) : w z = J (J (clamp w₂)) z :=
  eq_J_of_hasDerivWithinAt (J_continuous h.cont2)
    (fun x hx => by rw [← h.w1_eq hx]; exact h.d0 x hx) h.z0 hz

/-- Every solution satisfies the integral equation `w'' = w''(0) · exp (-2 J³ w'')`,
cf. Weyl's (12). -/
lemma rep (h : IsSol w w₁ w₂) {z : ℝ} (hz : 0 ≤ z) :
    w₂ z = w₂ 0 * Real.exp (-(2 * K (clamp w₂) z)) := by
  have hγ := h.cont2
  have hKc : Continuous (K (clamp w₂)) := K_continuous hγ
  have hK : ∀ x, HasDerivAt (fun x => Real.exp (2 * K (clamp w₂) x))
      (Real.exp (2 * K (clamp w₂) x) * (2 * J (J (clamp w₂)) x)) x := fun x =>
    ((J_hasDerivAt (J_continuous (J_continuous hγ)) x).const_mul 2).exp
  have hw2c : ContinuousOn w₂ (Ici 0) := fun x hx => (h.d2 x hx).continuousWithinAt
  have hc : ContinuousOn (fun x => w₂ x * Real.exp (2 * K (clamp w₂) x)) (Icc 0 z) :=
    (hw2c.mono Icc_subset_Ici_self).mul
      (by fun_prop : Continuous fun x => Real.exp (2 * K (clamp w₂) x)).continuousOn
  have hd : ∀ x ∈ Ico 0 z,
      HasDerivWithinAt (fun x => w₂ x * Real.exp (2 * K (clamp w₂) x)) 0 (Ici x) x := by
    intro x hx
    have := ((h.d2 x hx.1).mono (Ici_subset_Ici.2 hx.1)).mul (hK x).hasDerivWithinAt
    deriv_conv this
    rw [← h.w_eq hx.1]
    ring
  have key : w₂ z * Real.exp (2 * K (clamp w₂) z) = w₂ 0 * Real.exp (2 * K (clamp w₂) 0) :=
    constant_of_has_deriv_right_zero hc hd z (right_mem_Icc.2 hz)
  rw [K_apply_zero, mul_zero, Real.exp_zero, mul_one] at key
  rw [Real.exp_neg, ← key, mul_assoc, mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]

/-- Töpfer's scaling: with `w`, also `z ↦ l · w(l z)` is a solution. -/
lemma scale (h : IsSol w w₁ w₂) {l : ℝ} (hl : 0 < l) :
    IsSol (fun z => l * w (l * z)) (fun z => l ^ 2 * w₁ (l * z))
      (fun z => l ^ 3 * w₂ (l * z)) := by
  have hlin : ∀ z : ℝ, HasDerivWithinAt (fun z => l * z) l (Ici 0) z := fun z => by
    simpa using ((hasDerivAt_id z).const_mul l).hasDerivWithinAt
  have hmaps : MapsTo (fun z => l * z) (Ici (0 : ℝ)) (Ici 0) := fun x hx =>
    mul_nonneg hl.le hx
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, by simp [h.z0], by simp [h.z1]⟩
  · have := ((h.d0 (l * z) (mul_nonneg hl.le hz)).comp z (hlin z) hmaps).const_mul l
    deriv_conv this
    ring
  · have := ((h.d1 (l * z) (mul_nonneg hl.le hz)).comp z (hlin z) hmaps).const_mul (l ^ 2)
    deriv_conv this
    ring
  · have := ((h.d2 (l * z) (mul_nonneg hl.le hz)).comp z (hlin z) hmaps).const_mul (l ^ 3)
    deriv_conv this
    ring

/-- If `w'(z) → k > 0`, then `w''(0) > 0`: otherwise `w'' ≤ 0` throughout and `w' ≤ 0`. -/
lemma pos_of_tendsto (h : IsSol w w₁ w₂) {k : ℝ} (hk : 0 < k)
    (hlim : Tendsto w₁ atTop (𝓝 k)) : 0 < w₂ 0 := by
  by_contra hneg
  push Not at hneg
  have h2 : ∀ z, 0 ≤ z → w₂ z ≤ 0 := fun z hz => by
    rw [h.rep hz]
    exact mul_nonpos_of_nonpos_of_nonneg hneg (Real.exp_pos _).le
  have hd : ∀ x, 0 < x → HasDerivAt w₁ (w₂ x) x := fun x hx =>
    (h.d1 x hx.le).hasDerivAt (Ici_mem_nhds hx)
  have hanti : AntitoneOn w₁ (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun z hz => (h.d1 z hz).continuousWithinAt) (fun x hx => ?_) fun x hx => ?_
    · rw [interior_Ici] at hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ici] at hx
      rw [(hd x hx).deriv]
      exact h2 x (le_of_lt hx)
  have hk0 : k ≤ 0 := le_of_tendsto hlim ((eventually_ge_atTop 0).mono fun z hz => by
    have := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hz) hz
    rwa [h.z1] at this)
  linarith

end IsSol

/-- Uniqueness for the integral equation `γ = σ · exp (-2 J³ γ)` on `[0, ∞)`, `σ > 0`.
The difference of two solutions obeys Weyl's estimate (16) for every `n`, hence vanishes. -/
lemma fix_unique {γ δ : ℝ → ℝ} {σ : ℝ} (hσ : 0 < σ) (hγ : Continuous γ) (hδ : Continuous δ)
    (fγ : ∀ z, 0 ≤ z → γ z = σ * Real.exp (-(2 * K γ z)))
    (fδ : ∀ z, 0 ≤ z → δ z = σ * Real.exp (-(2 * K δ z))) {z : ℝ} (hz : 0 ≤ z) :
    γ z = δ z := by
  have pγ : ∀ t, 0 ≤ t → 0 ≤ γ t := fun t ht => by rw [fγ t ht]; positivity
  have pδ : ∀ t, 0 ≤ t → 0 ≤ δ t := fun t ht => by rw [fδ t ht]; positivity
  have uγ : ∀ t, 0 ≤ t → γ t ≤ σ := fun t ht => by
    rw [fγ t ht]
    refine mul_le_of_le_one_right hσ.le ?_
    rw [Real.exp_le_one_iff]
    linarith [K_nonneg pγ ht]
  have uδ : ∀ t, 0 ≤ t → δ t ≤ σ := fun t ht => by
    rw [fδ t ht]
    refine mul_le_of_le_one_right hσ.le ?_
    rw [Real.exp_le_one_iff]
    linarith [K_nonneg pδ ht]
  have key : ∀ (n : ℕ) (t : ℝ), 0 ≤ t → |γ t - δ t| ≤ σ ^ (n + 1) * a n * t ^ (3 * n) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have e : σ ^ (0 + 1) * a 0 * t ^ (3 * 0) = σ := by simp [a]
      rw [e, abs_le]
      constructor <;> linarith [pγ t ht, pδ t ht, uγ t ht, uδ t ht]
    | succ n ih =>
      intro t ht
      have hK := K_sub_le hγ hδ (d := fun s => σ ^ (n + 1) * a n * s ^ (3 * n))
        (by fun_prop) ih ht
      rw [K_monomial] at hK
      push_cast at hK
      have hp : 0 ≤ K γ t := K_nonneg pγ ht
      have hq : 0 ≤ K δ t := K_nonneg pδ ht
      rw [fγ t ht, fδ t ht, ← mul_sub, abs_mul, abs_of_pos hσ]
      calc σ * |Real.exp (-(2 * K γ t)) - Real.exp (-(2 * K δ t))|
          ≤ σ * |2 * K γ t - 2 * K δ t| :=
            mul_le_mul_of_nonneg_left
              (abs_exp_neg_sub_le (by positivity) (by positivity)) hσ.le
        _ = σ * (2 * |K γ t - K δ t|) := by rw [← mul_sub, abs_mul, abs_two]
        _ ≤ σ * (2 * (σ ^ (n + 1) * a n / ((3 * n + 1) * (3 * n + 2) * (3 * n + 3))
              * t ^ (3 * n + 3))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK zero_le_two) hσ.le
        _ = σ ^ (n + 1 + 1) * a (n + 1) * t ^ (3 * (n + 1)) := by
            rw [a]
            ring
  have hlim : Tendsto (fun n : ℕ => σ * ((2 * σ * z ^ 3) ^ n / n !)) atTop (𝓝 (σ * 0)) :=
    ((Real.summable_pow_div_factorial _).tendsto_atTop_zero).const_mul σ
  have hb : ∀ n : ℕ, |γ z - δ z| ≤ σ * ((2 * σ * z ^ 3) ^ n / n !) := fun n =>
    calc |γ z - δ z| ≤ σ ^ (n + 1) * a n * z ^ (3 * n) := key n z hz
      _ ≤ σ ^ (n + 1) * (2 ^ n / n !) * z ^ (3 * n) := by
          gcongr
          exact a_le n
      _ = σ * ((2 * σ * z ^ 3) ^ n / n !) := by ring
  have h0 := ge_of_tendsto' hlim hb
  rw [mul_zero] at h0
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

/-- Uniqueness for the initial-value problem with prescribed `w''(0) > 0`. -/
theorem IsSol.unique_ivp {u u₁ u₂ v v₁ v₂ : ℝ → ℝ} (hu : IsSol u u₁ u₂) (hv : IsSol v v₁ v₂)
    (h0 : u₂ 0 = v₂ 0) (hpos : 0 < u₂ 0) {z : ℝ} (hz : 0 ≤ z) :
    u z = v z ∧ u₁ z = v₁ z ∧ u₂ z = v₂ z := by
  have e : ∀ t, 0 ≤ t → clamp u₂ t = clamp v₂ t := fun t ht =>
    fix_unique hpos hu.cont2 hv.cont2
      (fun x hx => by rw [clamp_of_nonneg _ hx]; exact hu.rep hx)
      (fun x hx => by rw [clamp_of_nonneg _ hx, h0]; exact hv.rep hx) ht
  refine ⟨?_, ?_, ?_⟩
  · rw [hu.w_eq hz, hv.w_eq hz]
    exact J_congr (fun t ht => J_congr e ht) hz
  · rw [hu.w1_eq hz, hv.w1_eq hz]
    exact J_congr e hz
  · have := e z hz
    rwa [clamp_of_nonneg _ hz, clamp_of_nonneg _ hz] at this

lemma exists_cube_root {r : ℝ} (hr : 0 < r) : ∃ l : ℝ, 0 < l ∧ l ^ 3 = r := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3) (Icc 0 (r + 1)) :=
    (by fun_prop : Continuous fun x : ℝ => x ^ 3).continuousOn
  have hmem : r ∈ Icc ((fun x : ℝ => x ^ 3) 0) ((fun x : ℝ => x ^ 3) (r + 1)) := by
    have e : (r + 1) ^ 3 = r ^ 3 + 3 * r ^ 2 + 3 * r + 1 := by ring
    constructor
    · have h03 : (0 : ℝ) ^ 3 = 0 := by norm_num
      simp only
      rw [h03]
      exact hr.le
    · simp only; rw [e]; linarith [pow_pos hr 3, pow_pos hr 2]
  obtain ⟨l, hl, hl3⟩ := intermediate_value_Icc (by linarith) hc hmem
  refine ⟨l, lt_of_le_of_ne hl.1 ?_, hl3⟩
  rintro rfl
  simp at hl3
  linarith

/-- **Uniqueness for Weyl's problem `(A₀)`.**  Two solutions of `w''' + 2 w w'' = 0` on
`[0, ∞)` with `w(0) = w'(0) = 0` and `w'(z) → k > 0` coincide on `[0, ∞)`, together with
their first and second derivatives. -/
theorem weyl_A0_unique {k : ℝ} (hk : 0 < k) {u u₁ u₂ v v₁ v₂ : ℝ → ℝ}
    (hu : IsSol u u₁ u₂) (hul : Tendsto u₁ atTop (𝓝 k))
    (hv : IsSol v v₁ v₂) (hvl : Tendsto v₁ atTop (𝓝 k)) :
    ∀ z, 0 ≤ z → u z = v z ∧ u₁ z = v₁ z ∧ u₂ z = v₂ z := by
  have su := hu.pos_of_tendsto hk hul
  have sv := hv.pos_of_tendsto hk hvl
  obtain ⟨l, hl, hl3⟩ := exists_cube_root (div_pos sv su)
  have hs := hu.scale hl
  have h0 : (fun z => l ^ 3 * u₂ (l * z)) 0 = v₂ 0 := by
    simp only [mul_zero]
    rw [hl3, div_mul_cancel₀ _ su.ne']
  have hpos : 0 < (fun z => l ^ 3 * u₂ (l * z)) 0 := by rw [h0]; exact sv
  have huniq := fun (z : ℝ) (hz : 0 ≤ z) => hs.unique_ivp hv h0 hpos hz
  have hlim1 : Tendsto (fun z => l ^ 2 * u₁ (l * z)) atTop (𝓝 (l ^ 2 * k)) :=
    (hul.comp (tendsto_id.const_mul_atTop hl)).const_mul (l ^ 2)
  have hlim2 : Tendsto (fun z => l ^ 2 * u₁ (l * z)) atTop (𝓝 k) :=
    hvl.congr' ((eventually_ge_atTop 0).mono fun z hz => ((huniq z hz).2.1).symm)
  have hk' : l ^ 2 * k = k := tendsto_nhds_unique hlim1 hlim2
  have hl2 : l ^ 2 = 1 := by
    have : (l ^ 2 - 1) * k = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hk.ne'
  have hl1 : l = 1 := by
    have : (l - 1) * (l + 1) = 0 := by
      have e : (l - 1) * (l + 1) = l ^ 2 - 1 := by ring
      linarith
    rcases mul_eq_zero.1 this with h | h <;> linarith
  subst hl1
  intro z hz
  simpa using huniq z hz

/-! ## Blasius's problem: existence and uniqueness -/

/-- `(f, f₁, f₂)` solves Blasius's boundary-value problem `f''' + f f'' = 0` on `[0, ∞)`,
`f(0) = f'(0) = 0`, `f'(η) → 1`, where `f₁ = f'`, `f₂ = f''` (derivatives one-sided at `0`). -/
structure IsBlasiusSol (f f₁ f₂ : ℝ → ℝ) : Prop where
  d0 : ∀ η, 0 ≤ η → HasDerivWithinAt f (f₁ η) (Ici 0) η
  d1 : ∀ η, 0 ≤ η → HasDerivWithinAt f₁ (f₂ η) (Ici 0) η
  d2 : ∀ η, 0 ≤ η → HasDerivWithinAt f₂ (-(f η * f₂ η)) (Ici 0) η
  z0 : f 0 = 0
  z1 : f₁ 0 = 0
  lim : Tendsto f₁ atTop (𝓝 1)

lemma IsBlasiusSol.isSol {f f₁ f₂ : ℝ → ℝ} (h : IsBlasiusSol f f₁ f₂) :
    IsSol (fun z => f z / 2) (fun z => f₁ z / 2) (fun z => f₂ z / 2) := by
  refine ⟨fun z hz => (h.d0 z hz).div_const 2, fun z hz => (h.d1 z hz).div_const 2,
    fun z hz => ?_, by simp [h.z0], by simp [h.z1]⟩
  have := (h.d2 z hz).div_const 2
  deriv_conv this
  ring

/-- **Existence** of a solution of Blasius's problem. -/
theorem exists_isBlasiusSol : ∃ f f₁ f₂ : ℝ → ℝ, IsBlasiusSol f f₁ f₂ := by
  obtain ⟨f, f₁, f₂, h0, h1, h2, hf0, hf1, hlim⟩ := blasius_exists
  exact ⟨f, f₁, f₂, fun z _ => (h0 z).hasDerivWithinAt, fun z _ => (h1 z).hasDerivWithinAt,
    h2, hf0, hf1, hlim⟩

/-- **Uniqueness** of the solution of Blasius's problem on `[0, ∞)`. -/
theorem IsBlasiusSol.unique {f f₁ f₂ p p₁ p₂ : ℝ → ℝ} (hf : IsBlasiusSol f f₁ f₂)
    (hp : IsBlasiusSol p p₁ p₂) :
    ∀ η, 0 ≤ η → f η = p η ∧ f₁ η = p₁ η ∧ f₂ η = p₂ η := by
  intro η hη
  have key := weyl_A0_unique (k := 1 / 2) (by norm_num) hf.isSol (hf.lim.div_const 2)
    hp.isSol (hp.lim.div_const 2) η hη
  obtain ⟨k0, k1, k2⟩ := key
  exact ⟨by linarith, by linarith, by linarith⟩

end Blasius

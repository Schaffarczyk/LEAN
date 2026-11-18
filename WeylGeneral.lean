/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Weyl's generalisation to arbitrary order, and Goldstein's wake problem

A formalisation of §3 of

  H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
  Annals of Mathematics 43 (1942), 381–407.

The equation `f^(ν+1) + 2 f f^(ν) = 0` with initial data
`f(0) = c₀, …, f^(ν-1)(0) = c_{ν-1}`, `f^(ν)(0) = 1` (Weyl's (19), (21)) becomes, for
`g = f^(ν)` and `f = P + J^ν g` with the Taylor polynomial `P` of the initial data,

  `g = exp (-2Q - 2 J^(ν+1) g)`,   `Q = J P`                         (cf. Weyl's (22)).

We treat the slightly more general integral equation `g = q · exp (-2 J^m g)` on `[0, ∞)`
for a continuous `q ≥ 0` and `m ≥ 1`:

* `exists_fixq`: existence of a continuous solution (successive approximations with the
  estimate `|gₙ₊₁ - gₙ| ≤ Aⁿ⁺¹ 2ⁿ zⁿᵐ / (nm)!` on `[0, a]`, where `q ≤ A` there);
* `fixq_unique`: uniqueness;
* `weyl_order_exists`, `weyl_order_unique`: the initial-value problem for `g = f^(ν)`,
  with Weyl's inequality (23), `0 < g ≤ exp (-2Q)`;
* `goldstein_wake_exists`: Goldstein's wake problem (24), (25):
  `w''' + 2 w w'' - w'² = 0`, `w(0) = w''(0) = 0`, `w''(z) → a`.
-/
import BlasiusAsymptotics

open Set Filter Topology MeasureTheory
open scoped Nat

noncomputable section

namespace Blasius

/-! ## Iterated primitives -/

/-- The `m`-fold primitive `J^m g`. -/
def Jm (m : ℕ) (g : ℝ → ℝ) : ℝ → ℝ := J^[m] g

lemma Jm_zero (g : ℝ → ℝ) : Jm 0 g = g := rfl

lemma Jm_succ (m : ℕ) (g : ℝ → ℝ) : Jm (m + 1) g = J (Jm m g) :=
  Function.iterate_succ_apply' J m g

lemma Jm_succ' (m : ℕ) (g : ℝ → ℝ) : Jm (m + 1) g = Jm m (J g) :=
  Function.iterate_succ_apply J m g

lemma Jm_continuous {g : ℝ → ℝ} (hg : Continuous g) : ∀ m, Continuous (Jm m g)
  | 0 => hg
  | m + 1 => by
      rw [Jm_succ]
      exact J_continuous (Jm_continuous hg m)

@[simp] lemma Jm_succ_apply_zero (m : ℕ) (g : ℝ → ℝ) : Jm (m + 1) g 0 = 0 := by
  rw [Jm_succ]
  exact J_apply_zero _

lemma Jm_nonneg {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ t → 0 ≤ g t) :
    ∀ (m : ℕ) {z : ℝ}, 0 ≤ z → 0 ≤ Jm m g z
  | 0, z, hz => hg z hz
  | m + 1, z, hz => by
      rw [Jm_succ]
      exact J_nonneg (fun t ht => Jm_nonneg hg m ht) hz

lemma J_sub_le_on {u v d : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) (hd : Continuous d)
    {a : ℝ} (h : ∀ t, 0 ≤ t → t ≤ a → |u t - v t| ≤ d t) {z : ℝ} (hz : 0 ≤ z) (hza : z ≤ a) :
    |J u z - J v z| ≤ J d z := by
  unfold J
  rw [← intervalIntegral.integral_sub (hu.intervalIntegrable _ _) (hv.intervalIntegrable _ _)]
  calc |∫ t in (0 : ℝ)..z, (u t - v t)| ≤ ∫ t in (0 : ℝ)..z, |u t - v t| :=
        intervalIntegral.abs_integral_le_integral_abs hz
    _ ≤ ∫ t in (0 : ℝ)..z, d t :=
        intervalIntegral.integral_mono_on hz ((hu.sub hv).abs.intervalIntegrable _ _)
          (hd.intervalIntegrable _ _) fun t ht => h t ht.1 (ht.2.trans hza)

lemma Jm_sub_le_on {u v d : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) (hd : Continuous d)
    {a : ℝ} (h : ∀ t, 0 ≤ t → t ≤ a → |u t - v t| ≤ d t) :
    ∀ (m : ℕ) {z : ℝ}, 0 ≤ z → z ≤ a → |Jm m u z - Jm m v z| ≤ Jm m d z
  | 0, z, hz, hza => h z hz hza
  | m + 1, z, hz, hza => by
      rw [Jm_succ, Jm_succ, Jm_succ]
      exact J_sub_le_on (Jm_continuous hu m) (Jm_continuous hv m) (Jm_continuous hd m)
        (fun t ht hta => Jm_sub_le_on hu hv hd h m ht hta) hz hza

lemma Jm_monomial (c : ℝ) (k : ℕ) :
    ∀ m : ℕ, Jm m (fun t => c * t ^ k) = fun z => c * k ! / (k + m)! * z ^ (k + m)
  | 0 => by
      funext z
      have h1 : ((k ! : ℕ) : ℝ) ≠ 0 := by positivity
      simp only [Jm_zero, add_zero]
      field_simp
  | m + 1 => by
      rw [Jm_succ, Jm_monomial c k m, J_monomial']
      funext z
      have h1 : (((k + m)! : ℕ) : ℝ) ≠ 0 := by positivity
      have h2 : ((k + m : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      rw [show k + (m + 1) = k + m + 1 from rfl, Nat.factorial_succ]
      push_cast
      field_simp

/-- Dominated convergence for iterated primitives. -/
lemma Jm_tendsto : ∀ (m : ℕ) {F : ℕ → ℝ → ℝ} {f B : ℝ → ℝ}, (∀ n, Continuous (F n)) →
    Continuous B → (∀ n x, |F n x| ≤ B x) →
    (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    ∀ x, Tendsto (fun n => Jm m (F n) x) atTop (𝓝 (Jm m f x))
  | 0, _, _, _, _, _, _, hlim => hlim
  | m + 1, F, f, B, hF, hB, hb, hlim => by
      intro x
      simp only [Jm_succ']
      exact Jm_tendsto m (fun n => J_continuous (hF n)) (J_continuous hB).abs
        (fun n x => J_abs_le hB (hb n) x) (J_tendsto hF hB hb hlim) x

/-! ## The integral equation `g = q · exp (-2 J^m g)` -/

section Fix

variable {m : ℕ} {q : ℝ → ℝ}

/-- One step of the estimate: from a bound of order `n` for `u - v` on `[0, a]` to a bound of
order `n + 1` for the images under `g ↦ q · exp (-2 J^m g)`. -/
lemma contraction_step (hq0 : ∀ z, 0 ≤ q z) {a A : ℝ}
    (hA : ∀ t, 0 ≤ t → t ≤ a → q t ≤ A) {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (pu : ∀ t, 0 ≤ t → 0 ≤ u t) (pv : ∀ t, 0 ≤ t → 0 ≤ v t) {n : ℕ}
    (ih : ∀ t, 0 ≤ t → t ≤ a → |u t - v t| ≤ A ^ (n + 1) * 2 ^ n / (n * m)! * t ^ (n * m))
    {z : ℝ} (hz : 0 ≤ z) (hza : z ≤ a) :
    |q z * Real.exp (-(2 * Jm m u z)) - q z * Real.exp (-(2 * Jm m v z))|
      ≤ A ^ (n + 1 + 1) * 2 ^ (n + 1) / ((n + 1) * m)! * z ^ ((n + 1) * m) := by
  have hA0 : 0 ≤ A := (hq0 z).trans (hA z hz hza)
  have hK := Jm_sub_le_on hu hv
    (d := fun t => A ^ (n + 1) * 2 ^ n / (n * m)! * t ^ (n * m)) (by fun_prop) ih m hz hza
  rw [Jm_monomial] at hK
  have hp : 0 ≤ Jm m u z := Jm_nonneg pu m hz
  have hq' : 0 ≤ Jm m v z := Jm_nonneg pv m hz
  have hf1 : (((n * m)! : ℕ) : ℝ) ≠ 0 := by positivity
  have hf2 : (((n * m + m)! : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← mul_sub, abs_mul, abs_of_nonneg (hq0 z)]
  calc q z * |Real.exp (-(2 * Jm m u z)) - Real.exp (-(2 * Jm m v z))|
      ≤ A * |2 * Jm m u z - 2 * Jm m v z| :=
        mul_le_mul (hA z hz hza) (abs_exp_neg_sub_le (by positivity) (by positivity))
          (abs_nonneg _) hA0
    _ = A * (2 * |Jm m u z - Jm m v z|) := by rw [← mul_sub, abs_mul, abs_two]
    _ ≤ A * (2 * (A ^ (n + 1) * 2 ^ n / (n * m)! * (n * m)! / (n * m + m)! * z ^ (n * m + m))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK zero_le_two) hA0
    _ = A ^ (n + 1 + 1) * 2 ^ (n + 1) / ((n + 1) * m)! * z ^ ((n + 1) * m) := by
        rw [Nat.succ_mul]
        field_simp
        ring

/-- The clamped operator `g ↦ q · exp (-2 J^m g)`. -/
def Φq (m : ℕ) (q g : ℝ → ℝ) (z : ℝ) : ℝ :=
  q (max z 0) * Real.exp (-(2 * Jm m g (max z 0)))

lemma Φq_continuous (hq : Continuous q) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (Φq m q g) := by
  have hJ := Jm_continuous hg m
  unfold Φq
  fun_prop

lemma Φq_max (g : ℝ → ℝ) (z : ℝ) : Φq m q g (max z 0) = Φq m q g z := by
  unfold Φq
  rw [max_eq_left (le_max_right z 0)]

/-- Successive approximations. -/
def gs (m : ℕ) (q : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => Φq m q (gs m q n)

lemma gs_continuous (hq : Continuous q) : ∀ n, Continuous (gs m q n)
  | 0 => continuous_const
  | n + 1 => Φq_continuous hq (gs_continuous hq n)

lemma gs_nonneg (hq0 : ∀ z, 0 ≤ q z) (n : ℕ) (z : ℝ) : 0 ≤ gs m q n z := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact mul_nonneg (hq0 _) (Real.exp_pos _).le

lemma gs_le (hq0 : ∀ z, 0 ≤ q z) (n : ℕ) (z : ℝ) : gs m q n z ≤ q (max z 0) := by
  cases n with
  | zero => exact hq0 _
  | succ n =>
    refine mul_le_of_le_one_right (hq0 _) ?_
    rw [Real.exp_le_one_iff]
    have := Jm_nonneg (g := gs m q n) (fun t _ => gs_nonneg hq0 n t) m (le_max_right z 0)
    linarith

lemma gs_diff_on (hq : Continuous q) (hq0 : ∀ z, 0 ≤ q z) {a A : ℝ}
    (hA : ∀ t, 0 ≤ t → t ≤ a → q t ≤ A) : ∀ (n : ℕ) (z : ℝ), 0 ≤ z → z ≤ a →
    |gs m q (n + 1) z - gs m q n z| ≤ A ^ (n + 1) * 2 ^ n / (n * m)! * z ^ (n * m)
  | 0, z, hz, hza => by
      have h1 := gs_nonneg (m := m) hq0 1 z
      have h2 := gs_le (m := m) hq0 1 z
      rw [max_eq_left hz] at h2
      have h0 : gs m q 0 z = 0 := rfl
      rw [h0, sub_zero, abs_of_nonneg h1]
      simpa using h2.trans (hA z hz hza)
  | n + 1, z, hz, hza => by
      have h := contraction_step hq0 hA (gs_continuous hq (n + 1)) (gs_continuous hq n)
        (fun t _ => gs_nonneg hq0 _ t) (fun t _ => gs_nonneg hq0 _ t)
        (gs_diff_on hq hq0 hA n) hz hza
      have e : ∀ k, gs m q (k + 1) z
          = q z * Real.exp (-(2 * Jm m (gs m q k) z)) := fun k => by
        show Φq m q (gs m q k) z = _
        unfold Φq
        rw [max_eq_left hz]
      rw [e (n + 1), e n]
      exact h

lemma exists_bound_on (hq : Continuous q) (a : ℝ) : ∃ A, ∀ t, 0 ≤ t → t ≤ a → q t ≤ A := by
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := a)).bddAbove_image hq.continuousOn
  exact ⟨A, fun t h0 ha => hA ⟨t, ⟨h0, ha⟩, rfl⟩⟩

lemma bound_le_exp_series (hm : 1 ≤ m) {A a : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (n : ℕ) :
    A ^ (n + 1) * 2 ^ n / (n * m)! * a ^ (n * m) ≤ A * ((2 * A * a ^ m) ^ n / n !) := by
  have hfac : ((n ! : ℕ) : ℝ) ≤ ((n * m)! : ℕ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_mul_of_pos_right n hm)
  have hpos : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  calc A ^ (n + 1) * 2 ^ n / (n * m)! * a ^ (n * m)
      ≤ A ^ (n + 1) * 2 ^ n / n ! * a ^ (n * m) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact div_le_div_of_nonneg_left (by positivity) hpos hfac
    _ = A * ((2 * A * a ^ m) ^ n / n !) := by
        rw [mul_pow, mul_pow, ← pow_mul]
        ring

lemma gs_cauchy (hm : 1 ≤ m) (hq : Continuous q) (hq0 : ∀ z, 0 ≤ q z) (z : ℝ) :
    CauchySeq (fun n => gs m q n z) := by
  have ha : 0 ≤ max z 0 := le_max_right _ _
  obtain ⟨A, hA⟩ := exists_bound_on hq (max z 0)
  have hA0 : 0 ≤ A := (hq0 0).trans (hA 0 le_rfl ha)
  refine cauchySeq_of_dist_le_of_summable
    (fun n => A * ((2 * A * (max z 0) ^ m) ^ n / n !)) (fun n => ?_)
    ((Real.summable_pow_div_factorial _).mul_left A)
  rw [Real.dist_eq, abs_sub_comm]
  refine le_trans ?_ (bound_le_exp_series hm hA0 ha n)
  cases n with
  | zero =>
    have h1 := gs_nonneg (m := m) hq0 1 z
    have h2 := gs_le (m := m) hq0 1 z
    have h0 : gs m q 0 z = 0 := rfl
    rw [h0, sub_zero, abs_of_nonneg h1]
    simpa using h2.trans (hA _ ha le_rfl)
  | succ n =>
    have e1 : gs m q (n + 1 + 1) z = gs m q (n + 1 + 1) (max z 0) := (Φq_max _ z).symm
    have e2 : gs m q (n + 1) z = gs m q (n + 1) (max z 0) := (Φq_max _ z).symm
    rw [e1, e2]
    exact gs_diff_on hq hq0 hA (n + 1) _ ha le_rfl

/-- The limit of the successive approximations. -/
def gl (m : ℕ) (q : ℝ → ℝ) (z : ℝ) : ℝ := limUnder atTop (fun n => gs m q n z)

lemma gs_tendsto (hm : 1 ≤ m) (hq : Continuous q) (hq0 : ∀ z, 0 ≤ q z) (z : ℝ) :
    Tendsto (fun n => gs m q n z) atTop (𝓝 (gl m q z)) :=
  (gs_cauchy hm hq hq0 z).tendsto_limUnder

lemma gl_nonneg (hm : 1 ≤ m) (hq : Continuous q) (hq0 : ∀ z, 0 ≤ q z) (z : ℝ) :
    0 ≤ gl m q z :=
  ge_of_tendsto' (gs_tendsto hm hq hq0 z) fun n => gs_nonneg hq0 n z

lemma gl_le (hm : 1 ≤ m) (hq : Continuous q) (hq0 : ∀ z, 0 ≤ q z) (z : ℝ) :
    gl m q z ≤ q (max z 0) :=
  le_of_tendsto' (gs_tendsto hm hq hq0 z) fun n => gs_le hq0 n z

lemma gl_fix (hm : 1 ≤ m) (hq : Continuous q) (hq0 : ∀ z, 0 ≤ q z) (z : ℝ) :
    gl m q z = q (max z 0) * Real.exp (-(2 * Jm m (gl m q) (max z 0))) := by
  have hB : Continuous fun x => q (max x 0) := by fun_prop
  have hb : ∀ n x, |gs m q n x| ≤ q (max x 0) := fun n x => by
    rw [abs_of_nonneg (gs_nonneg hq0 n x)]
    exact gs_le hq0 n x
  have hK := Jm_tendsto m (fun n => gs_continuous hq n) hB hb (gs_tendsto hm hq hq0) (max z 0)
  have h1 : Tendsto (fun n => gs m q (n + 1) z) atTop (𝓝 (gl m q z)) :=
    (gs_tendsto hm hq hq0 z).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => gs m q (n + 1) z) atTop
      (𝓝 (q (max z 0) * Real.exp (-(2 * Jm m (gl m q) (max z 0))))) :=
    ((Real.continuous_exp.tendsto _).comp ((hK.const_mul 2).neg)).const_mul _
  exact tendsto_nhds_unique h1 h2

lemma gl_continuous (hm : 1 ≤ m) (hq : Continuous q) (hq0 : ∀ z, 0 ≤ q z) :
    Continuous (gl m q) := by
  have hB : Continuous fun x => q (max x 0) := by fun_prop
  have hmeas : Measurable (gl m q) :=
    measurable_of_tendsto_metrizable (fun n => (gs_continuous hq n).measurable)
      (tendsto_pi_nhds.2 (gs_tendsto hm hq hq0))
  have hint : ∀ a b, IntervalIntegrable (gl m q) volume a b := fun a b => by
    refine (hB.intervalIntegrable a b).mono_fun' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    show ‖gl m q x‖ ≤ q (max x 0)
    rw [Real.norm_eq_abs, abs_of_nonneg (gl_nonneg hm hq hq0 x)]
    exact gl_le hm hq hq0 x
  have hJ : Continuous (J (gl m q)) := intervalIntegral.continuous_primitive hint 0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hK : Continuous (Jm (m' + 1) (gl (m' + 1) q)) := by
    rw [Jm_succ']
    exact Jm_continuous hJ m'
  have h : gl (m' + 1) q = fun z =>
      q (max z 0) * Real.exp (-(2 * Jm (m' + 1) (gl (m' + 1) q) (max z 0))) :=
    funext (gl_fix hm hq hq0)
  rw [h]
  fun_prop

/-- **Existence** for the integral equation `g = q · exp (-2 J^m g)` on `[0, ∞)`. -/
theorem exists_fixq (hm : 1 ≤ m) (hq : Continuous q) (hq0 : ∀ z, 0 ≤ q z) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ z, 0 ≤ g z) ∧
      ∀ z, 0 ≤ z → g z = q z * Real.exp (-(2 * Jm m g z)) := by
  refine ⟨gl m q, gl_continuous hm hq hq0, gl_nonneg hm hq hq0, fun z hz => ?_⟩
  have := gl_fix hm hq hq0 z
  rwa [max_eq_left hz] at this

/-- **Uniqueness** for the integral equation `g = q · exp (-2 J^m g)` on `[0, ∞)`. -/
theorem fixq_unique (hm : 1 ≤ m) (hq : Continuous q) (hq0 : ∀ z, 0 ≤ q z) {γ δ : ℝ → ℝ}
    (hγ : Continuous γ) (hδ : Continuous δ)
    (fγ : ∀ z, 0 ≤ z → γ z = q z * Real.exp (-(2 * Jm m γ z)))
    (fδ : ∀ z, 0 ≤ z → δ z = q z * Real.exp (-(2 * Jm m δ z))) {z : ℝ} (hz : 0 ≤ z) :
    γ z = δ z := by
  obtain ⟨A, hA⟩ := exists_bound_on hq z
  have hA0 : 0 ≤ A := (hq0 0).trans (hA 0 le_rfl hz)
  have pγ : ∀ t, 0 ≤ t → 0 ≤ γ t := fun t ht => by
    rw [fγ t ht]
    exact mul_nonneg (hq0 t) (Real.exp_pos _).le
  have pδ : ∀ t, 0 ≤ t → 0 ≤ δ t := fun t ht => by
    rw [fδ t ht]
    exact mul_nonneg (hq0 t) (Real.exp_pos _).le
  have uγ : ∀ t, 0 ≤ t → γ t ≤ q t := fun t ht => by
    rw [fγ t ht]
    refine mul_le_of_le_one_right (hq0 t) ?_
    rw [Real.exp_le_one_iff]
    linarith [Jm_nonneg pγ m ht]
  have uδ : ∀ t, 0 ≤ t → δ t ≤ q t := fun t ht => by
    rw [fδ t ht]
    refine mul_le_of_le_one_right (hq0 t) ?_
    rw [Real.exp_le_one_iff]
    linarith [Jm_nonneg pδ m ht]
  have key : ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ z →
      |γ t - δ t| ≤ A ^ (n + 1) * 2 ^ n / (n * m)! * t ^ (n * m) := by
    intro n
    induction n with
    | zero =>
      intro t ht htz
      have e : A ^ (0 + 1) * 2 ^ 0 / ((0 * m)! : ℕ) * t ^ (0 * m) = A := by simp
      rw [e, abs_le]
      have := hA t ht htz
      constructor <;> linarith [pγ t ht, pδ t ht, uγ t ht, uδ t ht]
    | succ n ih =>
      intro t ht htz
      rw [fγ t ht, fδ t ht]
      exact contraction_step hq0 hA hγ hδ pγ pδ ih ht htz
  have hlim : Tendsto (fun n : ℕ => A * ((2 * A * z ^ m) ^ n / n !)) atTop (𝓝 (A * 0)) :=
    ((Real.summable_pow_div_factorial _).tendsto_atTop_zero).const_mul A
  have hb : ∀ n : ℕ, |γ z - δ z| ≤ A * ((2 * A * z ^ m) ^ n / n !) := fun n =>
    (key n z hz le_rfl).trans (bound_le_exp_series hm hA0 hz n)
  have h0 := ge_of_tendsto' hlim hb
  rw [mul_zero] at h0
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

end Fix

/-! ## The initial-value problem of order `ν + 1` -/

/-- **Weyl's (19), (21), (23).**  Let `P` be continuous (for Weyl: the Taylor polynomial
`c₀ + c₁ z + … + c_{ν-1} z^(ν-1)/(ν-1)!` of the initial data).  There is a continuous `g`
with `g(0) = 1` such that `f = P + J^ν g` satisfies `g' = -2 f g` on `[0, ∞)`; that is,
`f^(ν) = g` and `f^(ν+1) + 2 f f^(ν) = 0`.  Moreover `0 < g ≤ exp (-2 Q)` with `Q = J P`. -/
theorem weyl_order_exists (ν : ℕ) {P : ℝ → ℝ} (hP : Continuous P) :
    ∃ g : ℝ → ℝ, Continuous g ∧ g 0 = 1 ∧ (∀ z, 0 ≤ g z) ∧
      (∀ z, 0 ≤ z → HasDerivWithinAt g (-(2 * (P z + Jm ν g z) * g z)) (Ici 0) z) ∧
      ∀ z, 0 ≤ z → 0 < g z ∧ g z ≤ Real.exp (-(2 * J P z)) := by
  have hq : Continuous fun z => Real.exp (-(2 * J P z)) := by
    have := J_continuous hP
    fun_prop
  obtain ⟨g, hg, hg0, hfix⟩ := exists_fixq (m := ν + 1) (Nat.le_add_left 1 ν) hq
    (fun z => (Real.exp_pos _).le)
  have hF : Continuous fun t => P t + Jm ν g t := hP.add (Jm_continuous hg ν)
  have hJF : ∀ z, J (fun t => P t + Jm ν g t) z = J P z + Jm (ν + 1) g z := fun z => by
    rw [Jm_succ]
    exact intervalIntegral.integral_add (hP.intervalIntegrable _ _)
      ((Jm_continuous hg ν).intervalIntegrable _ _)
  have hrep : ∀ z, 0 ≤ z → g z = Real.exp (-(2 * J (fun t => P t + Jm ν g t) z)) :=
    fun z hz => by
      rw [hfix z hz, hJF, ← Real.exp_add]
      congr 1
      ring
  have hh : ∀ z, HasDerivAt (fun x => Real.exp (-(2 * J (fun t => P t + Jm ν g t) x)))
      (-(2 * (P z + Jm ν g z) * Real.exp (-(2 * J (fun t => P t + Jm ν g t) z)))) z :=
    fun z => by
      have h2 : HasDerivAt (fun x => -(2 * J (fun t => P t + Jm ν g t) x))
          (-(2 * (P z + Jm ν g z))) z := ((J_hasDerivAt hF z).const_mul 2).neg
      have h3 := h2.exp
      convert h3 using 1
      ring
  refine ⟨g, hg, ?_, hg0, fun z hz => ?_, fun z hz => ⟨?_, ?_⟩⟩
  · rw [hrep 0 le_rfl]
    simp
  · have h1 := (hh z).hasDerivWithinAt (s := Ici 0)
    rw [← hrep z hz] at h1
    exact h1.congr (fun x hx => hrep x hx) (hrep z hz)
  · rw [hrep z hz]
    exact Real.exp_pos _
  · rw [hfix z hz]
    refine mul_le_of_le_one_right (Real.exp_pos _).le ?_
    rw [Real.exp_le_one_iff]
    linarith [Jm_nonneg (fun t _ => hg0 t) (ν + 1) hz]

/-- Uniqueness for the initial-value problem of `weyl_order_exists`. -/
theorem weyl_order_unique (ν : ℕ) {P : ℝ → ℝ} (hP : Continuous P) {γ δ : ℝ → ℝ}
    (hγ : Continuous γ) (hδ : Continuous δ) (hγ0 : γ 0 = 1) (hδ0 : δ 0 = 1)
    (dγ : ∀ z, 0 ≤ z → HasDerivWithinAt γ (-(2 * (P z + Jm ν γ z) * γ z)) (Ici 0) z)
    (dδ : ∀ z, 0 ≤ z → HasDerivWithinAt δ (-(2 * (P z + Jm ν δ z) * δ z)) (Ici 0) z)
    {z : ℝ} (hz : 0 ≤ z) : γ z = δ z := by
  have hq : Continuous fun z => Real.exp (-(2 * J P z)) := by
    have := J_continuous hP
    fun_prop
  -- every solution satisfies the integral equation
  have rep : ∀ {g : ℝ → ℝ}, Continuous g → g 0 = 1 →
      (∀ z, 0 ≤ z → HasDerivWithinAt g (-(2 * (P z + Jm ν g z) * g z)) (Ici 0) z) →
      ∀ z, 0 ≤ z → g z = Real.exp (-(2 * J P z)) * Real.exp (-(2 * Jm (ν + 1) g z)) := by
    intro g hg hg0 dg z hz
    have hF : Continuous fun t => P t + Jm ν g t := hP.add (Jm_continuous hg ν)
    have hJF : ∀ z, J (fun t => P t + Jm ν g t) z = J P z + Jm (ν + 1) g z := fun z => by
      rw [Jm_succ]
      exact intervalIntegral.integral_add (hP.intervalIntegrable _ _)
        ((Jm_continuous hg ν).intervalIntegrable _ _)
    have hE : ∀ x, HasDerivAt (fun x => Real.exp (2 * J (fun t => P t + Jm ν g t) x))
        (Real.exp (2 * J (fun t => P t + Jm ν g t) x) * (2 * (P x + Jm ν g x))) x := fun x =>
      ((J_hasDerivAt hF x).const_mul 2).exp
    have hEc : Continuous fun x => Real.exp (2 * J (fun t => P t + Jm ν g t) x) := by
      have := J_continuous hF
      fun_prop
    have hc : ContinuousOn
        (fun x => g x * Real.exp (2 * J (fun t => P t + Jm ν g t) x)) (Icc 0 z) :=
      (hg.mul hEc).continuousOn
    have hd : ∀ x ∈ Ico 0 z, HasDerivWithinAt
        (fun x => g x * Real.exp (2 * J (fun t => P t + Jm ν g t) x)) 0 (Ici x) x := by
      intro x hx
      have := ((dg x hx.1).mono (Ici_subset_Ici.2 hx.1)).mul (hE x).hasDerivWithinAt
      convert this using 1
      ring
    have key : g z * Real.exp (2 * J (fun t => P t + Jm ν g t) z)
        = g 0 * Real.exp (2 * J (fun t => P t + Jm ν g t) 0) :=
      constant_of_has_deriv_right_zero hc hd z (right_mem_Icc.2 hz)
    rw [hg0, J_apply_zero, mul_zero, Real.exp_zero, mul_one] at key
    have hpos := Real.exp_pos (2 * J (fun t => P t + Jm ν g t) z)
    rw [← Real.exp_add, show -(2 * J P z) + -(2 * Jm (ν + 1) g z)
      = -(2 * J (fun t => P t + Jm ν g t) z) by rw [hJF]; ring, Real.exp_neg]
    field_simp
    linarith
  exact fixq_unique (m := ν + 1) (Nat.le_add_left 1 ν) hq (fun z => (Real.exp_pos _).le)
    hγ hδ (rep hγ hγ0 dγ) (rep hδ hδ0 dδ) hz

/-! ## Goldstein's wake problem -/

/-- **Goldstein's wake problem, Weyl's (24), (25).**  For every `a > 0` there is a function
`w` with `w''' + 2 w w'' - w'² = 0` on `[0, ∞)`, `w(0) = w''(0) = 0` and `w''(z) → a` as
`z → ∞`.  Here `w₁ = w'`, `w₂ = w''`. -/
theorem goldstein_wake_exists (a : ℝ) (ha : 0 < a) :
    ∃ w w₁ w₂ : ℝ → ℝ,
      (∀ z, HasDerivAt w (w₁ z) z) ∧
      (∀ z, HasDerivAt w₁ (w₂ z) z) ∧
      (∀ z, 0 ≤ z → HasDerivWithinAt w₂ (w₁ z ^ 2 - 2 * w z * w₂ z) (Ici 0) z) ∧
      w 0 = 0 ∧ w₂ 0 = 0 ∧ Tendsto w₂ atTop (𝓝 a) := by
  -- the case `ν = 3`, `P(z) = z`, i.e. `f(0) = 0`, `f'(0) = 1`, `f''(0) = 0`, `f'''(0) = 1`
  obtain ⟨g, hg, hg0, hgnn, hd, hbd⟩ := weyl_order_exists 3 (P := fun z => z) continuous_id
  have hJid : ∀ z : ℝ, J (fun z => z) z = z ^ 2 / 2 := fun z => by
    have := J_monomial 1 1 z
    simp only [one_mul, pow_one] at this
    rw [this]
    norm_num
    ring
  set f2 : ℝ → ℝ := J g with hf2
  set f1 : ℝ → ℝ := fun z => 1 + J f2 z with hf1
  set f0 : ℝ → ℝ := fun z => z + J (J f2) z with hf0
  have c2 : Continuous f2 := J_continuous hg
  have c1 : Continuous (J f2) := J_continuous c2
  have d2 : ∀ z, HasDerivAt f2 (g z) z := fun z => J_hasDerivAt hg z
  have d1 : ∀ z, HasDerivAt f1 (f2 z) z := fun z => (J_hasDerivAt c2 z).const_add 1
  have d0 : ∀ z, HasDerivAt f0 (f1 z) z := fun z =>
    (hasDerivAt_id z).add (J_hasDerivAt c1 z)
  have e3 : ∀ z, z + Jm 3 g z = f0 z := fun z => rfl
  -- first integral: `g = f1² - 2 f0 f2` on `[0, ∞)`
  have hint : ∀ z, 0 ≤ z → g z = f1 z ^ 2 - 2 * f0 z * f2 z := by
    intro z hz
    have hc : ContinuousOn (fun x => g x + 2 * f0 x * f2 x - f1 x ^ 2) (Icc 0 z) := by
      have h0 : Continuous f0 := continuous_iff_continuousAt.2 fun x => (d0 x).continuousAt
      have h1 : Continuous f1 := continuous_iff_continuousAt.2 fun x => (d1 x).continuousAt
      exact (by fun_prop : Continuous fun x => g x + 2 * f0 x * f2 x - f1 x ^ 2).continuousOn
    have hd' : ∀ x ∈ Ico 0 z,
        HasDerivWithinAt (fun x => g x + 2 * f0 x * f2 x - f1 x ^ 2) 0 (Ici x) x := by
      intro x hx
      have hgx := (hd x hx.1).mono (Ici_subset_Ici.2 hx.1)
      rw [e3] at hgx
      have := (hgx.add ((((d0 x).const_mul 2).mul (d2 x)).hasDerivWithinAt)).sub
        (((d1 x).pow 2).hasDerivWithinAt)
      convert this using 1
      simp
    have key : g z + 2 * f0 z * f2 z - f1 z ^ 2 = g 0 + 2 * f0 0 * f2 0 - f1 0 ^ 2 :=
      constant_of_has_deriv_right_zero hc hd' z (right_mem_Icc.2 hz)
    have z0 : f0 0 = 0 := by simp [hf0]
    have z1 : f1 0 = 1 := by simp [hf1]
    rw [hg0, z0, z1] at key
    linarith
  -- `f2 = f''` is monotone and bounded, hence convergent
  have m2 : Monotone f2 :=
    monotone_of_deriv_nonneg (fun z => (d2 z).differentiableAt) fun z => by
      rw [(d2 z).deriv]
      exact hgnn z
  have hanti : AntitoneOn (fun z => f2 z + Real.exp (1 - 2 * z) / 2) (Ici 0) :=
    antitoneOn_Ici_of_hasDerivAt (F' := fun z => g z - Real.exp (1 - 2 * z))
      (fun z => by
        have h1 : HasDerivAt (fun z : ℝ => 1 - 2 * z) (-2) z := by
          simpa using ((hasDerivAt_id z).const_mul 2).const_sub 1
        have h2 := h1.exp.div_const 2
        have h3 := (d2 z).add h2
        convert h3 using 1
        ring)
      (fun z hz => by
        have h1 := (hbd z (le_of_lt hz)).2
        rw [hJid] at h1
        have h2 : Real.exp (-(2 * (z ^ 2 / 2))) ≤ Real.exp (1 - 2 * z) := by
          rw [Real.exp_le_exp]
          nlinarith [sq_nonneg (z - 1)]
        linarith)
  have hbdd : BddAbove (range f2) := by
    refine ⟨Real.exp 1 / 2, ?_⟩
    rintro _ ⟨z, rfl⟩
    have z2 : f2 0 = 0 := J_apply_zero _
    have hE : 0 < Real.exp 1 / 2 := by positivity
    rcases le_total z 0 with hz | hz
    · have := m2 hz
      linarith
    · have := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hz) hz
      simp only [mul_zero, sub_zero] at this
      have hpos := Real.exp_pos (1 - 2 * z)
      linarith
  have hlim : Tendsto f2 atTop (𝓝 (⨆ z, f2 z)) := tendsto_atTop_ciSup m2 hbdd
  have hβ : 0 < ⨆ z, f2 z := by
    have h1 : 0 < f2 1 :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hg.intervalIntegrable _ _)
        (fun x hx => (hbd x (le_of_lt hx.1)).1) one_pos
    exact lt_of_lt_of_le h1 (le_ciSup hbdd 1)
  -- scaling
  obtain ⟨l, hl, hl3⟩ := exists_cube_root (div_pos ha hβ)
  have hlin : ∀ z : ℝ, HasDerivAt (fun z => l * z) l z := fun z => by
    simpa using (hasDerivAt_id z).const_mul l
  refine ⟨fun z => l * f0 (l * z), fun z => l ^ 2 * f1 (l * z), fun z => l ^ 3 * f2 (l * z),
    fun z => ?_, fun z => ?_, fun z hz => ?_, by simp [hf0], by simp [hf2], ?_⟩
  · have := ((d0 (l * z)).comp z (hlin z)).const_mul l
    convert this using 1
    ring
  · have := ((d1 (l * z)).comp z (hlin z)).const_mul (l ^ 2)
    convert this using 1
    ring
  · have := (((d2 (l * z)).comp z (hlin z)).const_mul (l ^ 3)).hasDerivWithinAt (s := Ici 0)
    convert this using 1
    rw [hint (l * z) (mul_nonneg hl.le hz)]
    ring
  · have h1 : Tendsto (fun z => l * z) atTop atTop := tendsto_id.const_mul_atTop hl
    have h2 := (hlim.comp h1).const_mul (l ^ 3)
    have e : l ^ 3 * (⨆ z, f2 z) = a := by rw [hl3, div_mul_cancel₀ _ hβ.ne']
    rw [e] at h2
    exact h2

end Blasius

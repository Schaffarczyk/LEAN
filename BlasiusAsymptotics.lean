/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Blasius's problem: monotonicity, decay and asymptotics

The remaining statements of §2 of

  H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
  Annals of Mathematics 43 (1942), 381–407,

for the unique solution `w` of problem `(A₀)`:
`w''' + 2 w w'' = 0`, `w(0) = w'(0) = 0`, `w'(z) → k`.

With Töpfer's solution `f` (`f'' (0) = 1`), `g = f''`, and Weyl's constants

  `β = ∫₀^∞ g`,   `β' = ∫₀^∞ z g(z) dz`,

we prove

* `g_le_gaussian`: `g(z) ≤ exp (γ - γ z² / 2)` with `γ = ∫₀¹ g` (Gaussian decay, p. 388);
* `f0_asymptotic`: `f(z) - (β z - β') → 0` (Weyl's (17));
* `β_ge_gamma`: `β ≥ ∫₀^∞ exp (-z³/3) dz = 3^(1/3) Γ(4/3)` (p. 388);
* `weyl_A0_structure`: every solution of `(A₀)` is `κ f(κ z)` with `κ² β = k`;
* `weyl_A0_second_deriv_zero`: `w''(0)² β³ = k³`, i.e. `w''(0) = α k^(3/2)`, `α = β^(-3/2)`
  (Weyl's (11));
* `weyl_A0_w1`, `weyl_A0_w2`: `w'` increases strictly from `0` towards `k`, `w''` is positive,
  decreasing and bounded by a Gaussian (the theorem on p. 406 for `λ = 0`);
* `weyl_A0_asymptotic`: `w(z) - (k z - κ β') → 0` (Weyl's (18)).
-/
import Blasius
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Gamma

open Set Filter Topology MeasureTheory

noncomputable section

namespace Blasius

/-! ## Monotonicity from the sign of the derivative -/

lemma monotoneOn_Ici_of_hasDerivAt {F F' : ℝ → ℝ} {a : ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
    (h : ∀ x, a < x → 0 ≤ F' x) : MonotoneOn F (Ici a) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici a)
    (continuous_iff_continuousAt.2 fun x => (hF x).continuousAt).continuousOn
    (fun x _ => (hF x).differentiableAt.differentiableWithinAt) fun x hx => ?_
  rw [interior_Ici] at hx
  rw [(hF x).deriv]
  exact h x hx

lemma antitoneOn_Ici_of_hasDerivAt {F F' : ℝ → ℝ} {a : ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
    (h : ∀ x, a < x → F' x ≤ 0) : AntitoneOn F (Ici a) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici a)
    (continuous_iff_continuousAt.2 fun x => (hF x).continuousAt).continuousOn
    (fun x _ => (hF x).differentiableAt.differentiableWithinAt) fun x hx => ?_
  rw [interior_Ici] at hx
  rw [(hF x).deriv]
  exact h x hx

/-! ## `f'' = g` is decreasing with Gaussian decay -/

lemma f0_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ f0 z :=
  J_nonneg (fun _ ht => f1_nonneg ht) hz

lemma h_pos (z : ℝ) : 0 < h z := Real.exp_pos _

lemma h_antitoneOn : AntitoneOn h (Ici 0) :=
  antitoneOn_Ici_of_hasDerivAt hasDerivAt_h fun x hx => by
    have h1 := f0_nonneg (le_of_lt hx)
    have h2 := h_pos x
    have : 0 ≤ 2 * f0 x * h x := by positivity
    linarith

/-- `f''` is non-increasing on `[0, ∞)`. -/
lemma g_antitoneOn : AntitoneOn g (Ici 0) := by
  intro x hx y hy hxy
  rw [g_eq_h hx, g_eq_h hy]
  exact h_antitoneOn hx hy hxy

/-- Weyl's constant `c = ∫₀^{z₀} g` for `z₀ = 1`. -/
def γ : ℝ := f1 1

lemma γ_pos : 0 < γ := f1_pos one_pos

lemma f0_ge {z : ℝ} (hz : 1 ≤ z) : γ * (z - 1) ≤ f0 z := by
  have hm : MonotoneOn (fun x => f0 x - γ * (x - 1)) (Ici 1) :=
    monotoneOn_Ici_of_hasDerivAt (F' := fun x => f1 x - γ)
      (fun x => by
        have h1 : HasDerivAt (fun x : ℝ => γ * (x - 1)) γ x := by
          simpa using ((hasDerivAt_id x).sub_const 1).const_mul γ
        exact (hasDerivAt_f0 x).sub h1)
      (fun x hx => sub_nonneg.2 (f1_mono (le_of_lt hx)))
  have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hz) hz
  simp only [sub_self, mul_zero, sub_zero] at this
  linarith [f0_nonneg zero_le_one]

lemma Jf0_ge {z : ℝ} (hz : 1 ≤ z) : γ * (z - 1) ^ 2 / 2 ≤ J f0 z := by
  have hm : MonotoneOn (fun x => J f0 x - γ * (x - 1) ^ 2 / 2) (Ici 1) :=
    monotoneOn_Ici_of_hasDerivAt (F' := fun x => f0 x - γ * (x - 1))
      (fun x => by
        have h1 : HasDerivAt (fun x : ℝ => γ * (x - 1) ^ 2 / 2) (γ * (x - 1)) x := by
          have := ((((hasDerivAt_id x).sub_const 1).pow 2).const_mul γ).div_const 2
          deriv_conv this
          simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
          ring
        exact (J_hasDerivAt f0_continuous x).sub h1)
      (fun x hx => sub_nonneg.2 (f0_ge (le_of_lt hx)))
  have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hz) hz
  simp only at this
  have h0 : 0 ≤ J f0 1 := J_nonneg (fun _ ht => f0_nonneg ht) zero_le_one
  nlinarith

/-- Weyl's bound `g(z) ≤ exp (-c (z - z₀)²)` for `z ≥ z₀`, with `z₀ = 1`, `c = γ`. -/
lemma g_le_gaussian_shift {z : ℝ} (hz : 1 ≤ z) : g z ≤ Real.exp (-(γ * (z - 1) ^ 2)) := by
  rw [g_eq_h (by linarith)]
  show Real.exp (-(2 * J f0 z)) ≤ _
  rw [Real.exp_le_exp]
  linarith [Jf0_ge hz]

/-- Gaussian decay of `f''` on all of `[0, ∞)`. -/
lemma g_le_gaussian {z : ℝ} (hz : 0 ≤ z) : g z ≤ Real.exp (γ - γ * z ^ 2 / 2) := by
  have hγ := γ_pos
  rcases le_total 1 z with h1 | h1
  · refine (g_le_gaussian_shift h1).trans ?_
    rw [Real.exp_le_exp]
    nlinarith [sq_nonneg (z - 2)]
  · refine (g_le_one z).trans ?_
    rw [← Real.exp_zero, Real.exp_le_exp]
    nlinarith [mul_nonneg hz (sub_nonneg.2 h1)]

lemma g_le_exp {z : ℝ} (hz : 0 ≤ z) : g z ≤ Real.exp (3 * γ / 2) * Real.exp (-γ * z) := by
  have hγ := γ_pos
  rw [← Real.exp_add]
  refine (g_le_gaussian hz).trans ?_
  rw [Real.exp_le_exp]
  nlinarith [sq_nonneg (z - 1)]

/-! ## The constants `β`, `β'` as improper integrals -/

lemma integrableOn_g : IntegrableOn g (Ioi 0) := by
  refine integrable_of_isBigO_exp_neg γ_pos g_continuous.continuousOn ?_
  refine Asymptotics.IsBigO.of_bound (Real.exp (3 * γ / 2)) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (g_nonneg x), Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact g_le_exp hx

lemma integrableOn_id_mul_g : IntegrableOn (fun t => t * g t) (Ioi 0) := by
  have hγ := γ_pos
  have hγ2 : 0 < γ / 2 := by positivity
  refine integrable_of_isBigO_exp_neg hγ2 (continuous_id.mul g_continuous).continuousOn ?_
  refine Asymptotics.IsBigO.of_bound (Real.exp (3 * γ / 2) * (2 / γ)) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (g_nonneg x)), Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have h1 : γ / 2 * x ≤ Real.exp (γ / 2 * x) := by linarith [Real.add_one_le_exp (γ / 2 * x)]
  have hE : 0 < Real.exp (γ / 2 * x) := Real.exp_pos _
  have h2 : x * Real.exp (-(γ / 2 * x)) ≤ 2 / γ := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hE hγ]
    nlinarith
  have h3 : Real.exp (-γ * x) = Real.exp (-(γ / 2 * x)) * Real.exp (-(γ / 2) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc x * g x ≤ x * (Real.exp (3 * γ / 2) * Real.exp (-γ * x)) :=
        mul_le_mul_of_nonneg_left (g_le_exp hx) hx
    _ = Real.exp (3 * γ / 2) * (x * Real.exp (-(γ / 2 * x))) * Real.exp (-(γ / 2) * x) := by
        rw [h3]
        ring
    _ ≤ Real.exp (3 * γ / 2) * (2 / γ) * Real.exp (-(γ / 2) * x) := by
        gcongr

/-- `β = ∫₀^∞ f''`. -/
lemma β_eq_integral : β = ∫ t in Ioi (0 : ℝ), g t :=
  tendsto_nhds_unique f1_tendsto
    (intervalIntegral_tendsto_integral_Ioi 0 integrableOn_g tendsto_id)

/-- Weyl's constant `β' = ∫₀^∞ z f''(z) dz`. -/
def β' : ℝ := ∫ t in Ioi (0 : ℝ), t * g t

/-- `E(z) = z f'(z) - f(z) = ∫₀ᶻ t g(t) dt`. -/
def E (z : ℝ) : ℝ := z * f1 z - f0 z

lemma hasDerivAt_E (z : ℝ) : HasDerivAt E (z * g z) z := by
  have := ((hasDerivAt_id z).mul (hasDerivAt_f1 z)).sub (hasDerivAt_f0 z)
  deriv_conv this
  simp only [id]
  ring

lemma E_eq (z : ℝ) : E z = ∫ t in (0 : ℝ)..z, t * g t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_E x)
    ((continuous_id.mul g_continuous).intervalIntegrable _ _)]
  simp [E]

lemma E_tendsto : Tendsto E atTop (𝓝 β') :=
  (intervalIntegral_tendsto_integral_Ioi 0 integrableOn_id_mul_g tendsto_id).congr
    fun z => (E_eq z).symm

lemma f1_le_β (z : ℝ) : f1 z ≤ β := le_ciSup f1_bddAbove z

lemma f1_strictMono : StrictMono f1 :=
  strictMono_of_deriv_pos fun z => by
    rw [(hasDerivAt_f1 z).deriv]
    exact g_pos z

lemma f1_lt_β (z : ℝ) : f1 z < β :=
  lt_of_lt_of_le (f1_strictMono (lt_add_one z)) (f1_le_β _)

lemma mul_β_sub_f1_le (z : ℝ) : z * (β - f1 z) ≤ β' - E z := by
  have hm : MonotoneOn (fun y => E y - z * f1 y) (Ici z) :=
    monotoneOn_Ici_of_hasDerivAt (F' := fun y => y * g y - z * g y)
      (fun y => (hasDerivAt_E y).sub ((hasDerivAt_f1 y).const_mul z))
      (fun y hy => by
        have := mul_nonneg (sub_nonneg.2 (le_of_lt hy)) (g_nonneg y)
        nlinarith)
  have h1 : Tendsto (fun y => z * (f1 y - f1 z)) atTop (𝓝 (z * (β - f1 z))) :=
    (f1_tendsto.sub_const _).const_mul z
  have h2 : Tendsto (fun y => E y - E z) atTop (𝓝 (β' - E z)) := E_tendsto.sub_const _
  refine le_of_tendsto_of_tendsto h1 h2 ((eventually_ge_atTop z).mono fun y hy => ?_)
  have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hy) hy
  simp only at this
  linarith

/-- **Weyl's asymptotic formula (17)**: `f(z) ~ β z - β'`, in the strong sense that the
difference tends to zero. -/
theorem f0_asymptotic : Tendsto (fun z => f0 z - (β * z - β')) atTop (𝓝 0) := by
  have h2 : Tendsto (fun z => β' - E z) atTop (𝓝 0) := by
    simpa using E_tendsto.const_sub β'
  have h1 : Tendsto (fun z => z * (β - f1 z)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      ((eventually_ge_atTop 0).mono fun z hz => mul_nonneg hz (sub_nonneg.2 (f1_le_β z)))
      (Eventually.of_forall fun z => mul_β_sub_f1_le z)
  have h3 := h2.sub h1
  rw [sub_zero] at h3
  refine h3.congr fun z => ?_
  simp only [E]
  ring

/-! ## The lower bound `β ≥ ∫₀^∞ exp (-z³/3) dz` -/

lemma J_mono {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (h : ∀ t, 0 ≤ t → u t ≤ v t) {z : ℝ} (hz : 0 ≤ z) : J u z ≤ J v z :=
  intervalIntegral.integral_mono_on hz (hu.intervalIntegrable _ _) (hv.intervalIntegrable _ _)
    fun t ht => h t ht.1

lemma K_mono {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (h : ∀ t, 0 ≤ t → u t ≤ v t) {z : ℝ} (hz : 0 ≤ z) : K u z ≤ K v z :=
  J_mono (J_continuous (J_continuous hu)) (J_continuous (J_continuous hv))
    (fun _ ht => J_mono (J_continuous hu) (J_continuous hv)
      (fun _ hs => J_mono hu hv h hs) ht) hz

lemma K_one (z : ℝ) : K (fun _ => (1 : ℝ)) z = z ^ 3 / 6 := by
  have e : (fun _ : ℝ => (1 : ℝ)) = fun t => 1 * t ^ 0 := by
    funext t
    simp
  rw [e, K_monomial]
  norm_num
  ring

/-- `g ≥ g₂ = exp (-z³/3)` (Weyl, p. 388). -/
lemma g_ge {z : ℝ} (hz : 0 ≤ z) : Real.exp (-(z ^ 3 / 3)) ≤ g z := by
  rw [g_fix z, max_eq_left hz, Real.exp_le_exp]
  have := K_mono g_continuous continuous_const (fun t _ => g_le_one t) hz
  rw [K_one] at this
  linarith

lemma integrableOn_exp_neg_cube : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 3 / 3))) (Ioi 0) := by
  refine Integrable.mono' integrableOn_g
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(t ^ 3 / 3))).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact g_ge (le_of_lt hx)

/-- `β ≥ B = ∫₀^∞ exp (-z³/3) dz` (Weyl, p. 388). -/
theorem β_ge : ∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3)) ≤ β := by
  rw [β_eq_integral]
  exact setIntegral_mono_on integrableOn_exp_neg_cube integrableOn_g measurableSet_Ioi
    fun x hx => g_ge (le_of_lt hx)

/-- Weyl's value `B = 3^(1/3) Γ(4/3)`. -/
lemma integral_exp_neg_cube :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3)) = (3 : ℝ) ^ (1 / 3 : ℝ) * Real.Gamma (4 / 3) := by
  have h := integral_exp_neg_mul_rpow (p := 3) (b := 1 / 3) (by norm_num) (by norm_num)
  have e : ∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3))
      = ∫ t in Ioi (0 : ℝ), Real.exp (-(1 / 3) * t ^ (3 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have : t ^ (3 : ℝ) = t ^ 3 := by
      rw [← Real.rpow_natCast]
      norm_num
    simp only [this]
    congr 1
    ring
  rw [e, h]
  have h3 : (1 / 3 : ℝ) ^ (-1 / 3 : ℝ) = (3 : ℝ) ^ (1 / 3 : ℝ) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num
  rw [h3]
  norm_num

theorem β_ge_gamma : (3 : ℝ) ^ (1 / 3 : ℝ) * Real.Gamma (4 / 3) ≤ β := by
  rw [← integral_exp_neg_cube]
  exact β_ge

/-! ## Structure of the solutions of `(A₀)` -/

lemma isSol_base : IsSol f0 f1 g :=
  ⟨fun z _ => (hasDerivAt_f0 z).hasDerivWithinAt, fun z _ => (hasDerivAt_f1 z).hasDerivWithinAt,
    fun _ hz => hasDerivWithinAt_g hz, f0_zero, f1_zero⟩

/-- Töpfer's scaling factor `κ = (k/β)^(1/2)`. -/
def κ (k : ℝ) : ℝ := Real.sqrt (k / β)

lemma κ_pos {k : ℝ} (hk : 0 < k) : 0 < κ k := Real.sqrt_pos.2 (div_pos hk β_pos)

lemma κ_sq {k : ℝ} (hk : 0 < k) : κ k ^ 2 * β = k := by
  rw [κ, Real.sq_sqrt (div_pos hk β_pos).le, div_mul_cancel₀ _ β_pos.ne']

/-- Every solution of `(A₀)` is Töpfer's scaled solution `κ f(κ z)`. -/
theorem weyl_A0_structure {k : ℝ} (hk : 0 < k) {w w₁ w₂ : ℝ → ℝ} (h : IsSol w w₁ w₂)
    (hlim : Tendsto w₁ atTop (𝓝 k)) :
    ∀ z, 0 ≤ z → w z = κ k * f0 (κ k * z) ∧ w₁ z = κ k ^ 2 * f1 (κ k * z) ∧
      w₂ z = κ k ^ 3 * g (κ k * z) := by
  have hκ := κ_pos hk
  have hl : Tendsto (fun z => κ k ^ 2 * f1 (κ k * z)) atTop (𝓝 k) := by
    have h2 := (f1_tendsto.comp (tendsto_id.const_mul_atTop hκ)).const_mul (κ k ^ 2)
    rw [κ_sq hk] at h2
    exact h2
  exact weyl_A0_unique hk h hlim (isSol_base.scale hκ) hl

section Properties

variable {k : ℝ} {w w₁ w₂ : ℝ → ℝ}

/-- **Weyl's (11)**: `w''(0) = α k^(3/2)` with `α = β^(-3/2)`, stated without roots as
`w''(0)² β³ = k³`. -/
theorem weyl_A0_second_deriv_zero (hk : 0 < k) (h : IsSol w w₁ w₂)
    (hlim : Tendsto w₁ atTop (𝓝 k)) : 0 < w₂ 0 ∧ w₂ 0 ^ 2 * β ^ 3 = k ^ 3 := by
  have hκ := κ_pos hk
  have h0 := (weyl_A0_structure hk h hlim 0 le_rfl).2.2
  rw [mul_zero, g_zero, mul_one] at h0
  refine ⟨by rw [h0]; positivity, ?_⟩
  rw [h0]
  calc (κ k ^ 3) ^ 2 * β ^ 3 = (κ k ^ 2 * β) ^ 3 := by ring
    _ = k ^ 3 := by rw [κ_sq hk]

/-- `w'` increases strictly on `[0, ∞)`, from `0` towards (but never reaching) `k`. -/
theorem weyl_A0_w1 (hk : 0 < k) (h : IsSol w w₁ w₂) (hlim : Tendsto w₁ atTop (𝓝 k)) :
    StrictMonoOn w₁ (Ici 0) ∧ ∀ z, 0 ≤ z → w₁ z < k := by
  have hκ := κ_pos hk
  have hs := weyl_A0_structure hk h hlim
  refine ⟨fun x hx y hy hxy => ?_, fun z hz => ?_⟩
  · rw [(hs x hx).2.1, (hs y hy).2.1]
    exact mul_lt_mul_of_pos_left (f1_strictMono (mul_lt_mul_of_pos_left hxy hκ)) (by positivity)
  · rw [(hs z hz).2.1]
    calc κ k ^ 2 * f1 (κ k * z) < κ k ^ 2 * β :=
          mul_lt_mul_of_pos_left (f1_lt_β _) (by positivity)
      _ = k := κ_sq hk

/-- `w''` is positive and non-increasing on `[0, ∞)` and decays like a Gaussian. -/
theorem weyl_A0_w2 (hk : 0 < k) (h : IsSol w w₁ w₂) (hlim : Tendsto w₁ atTop (𝓝 k)) :
    (∀ z, 0 ≤ z → 0 < w₂ z) ∧ AntitoneOn w₂ (Ici 0) ∧
      ∃ C c : ℝ, 0 < c ∧ ∀ z, 0 ≤ z → w₂ z ≤ C * Real.exp (-(c * z ^ 2)) := by
  have hκ := κ_pos hk
  have hγ := γ_pos
  have hs := weyl_A0_structure hk h hlim
  refine ⟨fun z hz => ?_, fun x hx y hy hxy => ?_,
    κ k ^ 3 * Real.exp γ, γ * κ k ^ 2 / 2, by positivity, fun z hz => ?_⟩
  · rw [(hs z hz).2.2]
    exact mul_pos (by positivity) (g_pos _)
  · rw [(hs x hx).2.2, (hs y hy).2.2]
    exact mul_le_mul_of_nonneg_left
      (g_antitoneOn (mem_Ici.2 (mul_nonneg hκ.le hx)) (mem_Ici.2 (mul_nonneg hκ.le hy))
        (mul_le_mul_of_nonneg_left hxy hκ.le)) (by positivity)
  · rw [(hs z hz).2.2, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left ((g_le_gaussian (mul_nonneg hκ.le hz)).trans ?_)
      (by positivity)
    rw [Real.exp_le_exp]
    apply le_of_eq
    ring

/-- **Weyl's asymptotic formula (18)**: `w(z) ~ k z - (β'/β^(1/2)) k^(1/2)`; here
`κ k * β' = (k/β)^(1/2) β'`. -/
theorem weyl_A0_asymptotic (hk : 0 < k) (h : IsSol w w₁ w₂) (hlim : Tendsto w₁ atTop (𝓝 k)) :
    Tendsto (fun z => w z - (k * z - κ k * β')) atTop (𝓝 0) := by
  have hκ := κ_pos hk
  have hs := weyl_A0_structure hk h hlim
  have h1 := (f0_asymptotic.comp (tendsto_id.const_mul_atTop hκ)).const_mul (κ k)
  rw [mul_zero] at h1
  refine h1.congr' ((eventually_ge_atTop 0).mono fun z hz => ?_)
  simp only [Function.comp, id]
  rw [(hs z hz).1]
  have e : k = κ k ^ 2 * β := (κ_sq hk).symm
  linear_combination z * e

end Properties

end Blasius

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Weyl's auxiliary theorem (§6), in abstract form

Reference: H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
Annals of Mathematics 43 (1942), 381–407, pp. 398–401.

For the cooperative system `ψ' = a χ`, `χ' = b ψ` with continuous `a ≥ 1`, `b ≥ 0`
(see `LinearSystem.lean` for the relation to Weyl's equation (37)) let `η`, `ϑ` be the
solutions with initial values `(1, 0)` and `(0, 1)`.  Weyl's auxiliary theorem states that
there is exactly one solution `ω = η - l ϑ` with

  `ψ(0) = 1`,   `ψ ≥ 0`,   `χ ≤ 0`   on `[0, ∞)`                          (Weyl's (40)).

* `lw a b`: the number `l = lim_{T → ∞} η(T) / ϑ(T)`;
* `om_sign`: `ω = η - l ϑ` has `ψ ≥ 0`, `χ ≤ 0`;
* `lw_unique`: no other multiple of `ϑ` has this property;
* `omψ_le_one`: `ψ_ω ≤ 1` (Weyl's (45), `p ω ≤ 1`).

The solutions `φ^(a)` of Weyl's proof (with `φ(a) = 0`) appear in `comb_sign`; their sign
is obtained from the positivity of cooperative systems after time reversal, instead of
Weyl's "Dirichlet integral" (43).
-/
import LinearSystem

open Set Filter Topology MeasureTheory

noncomputable section

namespace Blasius

lemma IsLinOn.sub_mul {a b : ℝ → ℝ} {T : ℝ} {ψ₁ χ₁ ψ₂ χ₂ : ℝ → ℝ}
    (h₁ : IsLinOn a b T ψ₁ χ₁) (h₂ : IsLinOn a b T ψ₂ χ₂) (c : ℝ) :
    IsLinOn a b T (fun z => ψ₁ z - c * ψ₂ z) (fun z => χ₁ z - c * χ₂ z) := by
  constructor
  · intro z h0 h1
    have := (h₁.dψ z h0 h1).sub ((h₂.dψ z h0 h1).const_mul c)
    deriv_conv this
    ring
  · intro z h0 h1
    have := (h₁.dχ z h0 h1).sub ((h₂.dχ z h0 h1).const_mul c)
    deriv_conv this
    ring

/-- Hypotheses on the coefficients: continuous, `a ≥ 1`, `b ≥ 0`. -/
structure Coop (a b : ℝ → ℝ) : Prop where
  ca : Continuous a
  cb : Continuous b
  a1 : ∀ z, 1 ≤ a z
  b0 : ∀ z, 0 ≤ b z

/-- Weyl's `η` (as `p η`). -/
def etaψ (a b : ℝ → ℝ) : ℝ → ℝ := solψ a b 1 0

/-- Weyl's `η₁ / p`. -/
def etaχ (a b : ℝ → ℝ) : ℝ → ℝ := solχ a b 1 0

/-- Weyl's `ϑ` (as `p ϑ`). -/
def thψ (a b : ℝ → ℝ) : ℝ → ℝ := solψ a b 0 1

/-- Weyl's `ϑ₁ / p`. -/
def thχ (a b : ℝ → ℝ) : ℝ → ℝ := solχ a b 0 1

namespace Coop

variable {a b : ℝ → ℝ} (h : Coop a b)
include h

lemma a0 (z : ℝ) : 0 ≤ a z := zero_le_one.trans (h.a1 z)

lemma eta (T : ℝ) : IsLinOn a b T (etaψ a b) (etaχ a b) := sol_isLinOn 1 0 h.ca h.cb T

lemma theta (T : ℝ) : IsLinOn a b T (thψ a b) (thχ a b) := sol_isLinOn 0 1 h.ca h.cb T

omit h in
@[simp] lemma etaψ_zero : etaψ a b 0 = 1 := solψ_zero 1 0

omit h in
@[simp] lemma etaχ_zero : etaχ a b 0 = 0 := solχ_zero 1 0

omit h in
@[simp] lemma thψ_zero : thψ a b 0 = 0 := solψ_zero 0 1

omit h in
@[simp] lemma thχ_zero : thχ a b 0 = 1 := solχ_zero 0 1

lemma eta_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ etaψ a b z ∧ 0 ≤ etaχ a b z :=
  sol_nonneg 1 0 h.ca h.cb zero_le_one le_rfl h.a0 h.b0 hz

lemma theta_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ thψ a b z ∧ 1 ≤ thχ a b z :=
  sol_nonneg 0 1 h.ca h.cb le_rfl zero_le_one h.a0 h.b0 hz

/-- `p ϑ ≥ z` (Weyl, p. 401). -/
lemma thψ_ge {z : ℝ} (hz : 0 ≤ z) : z ≤ thψ a b z := by
  have hm := monotoneOn_Icc_of_hasDerivAt (F := fun x => thψ a b x - x)
    (F' := fun x => a x * thχ a b x - 1) (s := 0) (t := z)
    (fun x h0 h1 => ((h.theta z).dψ x h0 h1).sub (hasDerivAt_id x))
    (fun x h0 _ => by
      have := (h.theta_nonneg h0).2
      have := h.a1 x
      nlinarith)
  have := hm (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
  simp only [thψ_zero, sub_zero] at this
  linarith

lemma thψ_pos {z : ℝ} (hz : 0 < z) : 0 < thψ a b z := lt_of_lt_of_le hz (h.thψ_ge hz.le)

lemma etaψ_ge_one {z : ℝ} (hz : 0 ≤ z) : 1 ≤ etaψ a b z := by
  have hm := monotoneOn_Icc_of_hasDerivAt (F := etaψ a b) (s := 0) (t := z)
    (fun x h0 h1 => (h.eta z).dψ x h0 h1)
    (fun x h0 _ => mul_nonneg (h.a0 x) (h.eta_nonneg h0).2)
  have := hm (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
  simpa using this

/-- The Wronskian `η ϑ₁ - ϑ η₁` is identically `1`. -/
lemma wronskian {z : ℝ} (hz : 0 ≤ z) :
    etaψ a b z * thχ a b z - thψ a b z * etaχ a b z = 1 := by
  have := eq_of_hasDerivAt_zero (F := fun x => etaψ a b x * thχ a b x - thψ a b x * etaχ a b x)
    hz (fun x h0 h1 => by
      have := (((h.eta z).dψ x h0 h1).mul ((h.theta z).dχ x h0 h1)).sub
        (((h.theta z).dψ x h0 h1).mul ((h.eta z).dχ x h0 h1))
      deriv_conv this
      ring)
  simpa using this

end Coop

/-- Weyl's `l_a = η(a) / ϑ(a)`. -/
def Lw (a b : ℝ → ℝ) (T : ℝ) : ℝ := etaψ a b T / thψ a b T

/-- Weyl's constant `l = lim_{a → ∞} l_a = -ω'(0)`. -/
def lw (a b : ℝ → ℝ) : ℝ := ⨅ n : ℕ, Lw a b (n + 1)

/-- Weyl's `p ω`, `ω = η - l ϑ`. -/
def omψ (a b : ℝ → ℝ) (z : ℝ) : ℝ := etaψ a b z - lw a b * thψ a b z

/-- Weyl's `ω₁ / p`. -/
def omχ (a b : ℝ → ℝ) (z : ℝ) : ℝ := etaχ a b z - lw a b * thχ a b z

namespace Coop

variable {a b : ℝ → ℝ} (h : Coop a b)
include h

/-- Weyl's solution `φ^(T)` with `φ(T) = 0` is positive with `φ₁ ≤ 0` on `[0, T]`. -/
lemma comb_sign {T z : ℝ} (hT : 0 < T) (hz : 0 ≤ z) (hzT : z ≤ T) :
    0 ≤ etaψ a b z - Lw a b T * thψ a b z ∧ etaχ a b z - Lw a b T * thχ a b z ≤ 0 := by
  have hpos := h.thψ_pos hT
  have hrev := ((h.eta T).sub_mul (h.theta T) (Lw a b T)).reverse
  have hca : Continuous fun t => a (T - t) := h.ca.comp (continuous_const.sub continuous_id)
  have hcb : Continuous fun t => b (T - t) := h.cb.comp (continuous_const.sub continuous_id)
  have h0 : etaψ a b T - Lw a b T * thψ a b T = 0 := by
    rw [Lw, div_mul_cancel₀ _ hpos.ne']
    ring
  have h1 : -(etaχ a b T - Lw a b T * thχ a b T) = 1 / thψ a b T := by
    have hw := h.wronskian hT.le
    rw [Lw]
    field_simp
    linarith
  have hnn := hrev.nonneg hca hcb (fun t => h.a0 _) (fun t => h.b0 _)
    (by simp only [sub_zero]; rw [h0])
    (by simp only [sub_zero]; rw [h1]; positivity)
    (z := T - z) (by linarith) (by linarith)
  simp only [sub_sub_cancel, sub_zero] at hnn
  rw [h1] at hnn
  have : (0 : ℝ) ≤ 1 / thψ a b T := by positivity
  exact ⟨hnn.1, by linarith [hnn.2]⟩

lemma Lw_nonneg {T : ℝ} (hT : 0 < T) : 0 ≤ Lw a b T :=
  div_nonneg (h.eta_nonneg hT.le).1 (h.thψ_pos hT).le

lemma Lw_antitone {T₁ T₂ : ℝ} (hT : 0 < T₁) (h12 : T₁ ≤ T₂) : Lw a b T₂ ≤ Lw a b T₁ := by
  have := (h.comb_sign (hT.trans_le h12) hT.le h12).1
  show Lw a b T₂ ≤ etaψ a b T₁ / thψ a b T₁
  rw [le_div_iff₀ (h.thψ_pos hT)]
  linarith

lemma lw_tendsto : Tendsto (fun n : ℕ => Lw a b (n + 1)) atTop (𝓝 (lw a b)) :=
  tendsto_atTop_ciInf
    (fun m n hmn => h.Lw_antitone (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn))
    ⟨0, by rintro _ ⟨n, rfl⟩; exact h.Lw_nonneg (by positivity)⟩

lemma lw_nonneg : 0 ≤ lw a b := le_ciInf fun n => h.Lw_nonneg (by positivity)

lemma om (T : ℝ) : IsLinOn a b T (omψ a b) (omχ a b) :=
  (h.eta T).sub_mul (h.theta T) (lw a b)

omit h in
@[simp] lemma omψ_zero : omψ a b 0 = 1 := by simp [omψ]

omit h in
@[simp] lemma omχ_zero : omχ a b 0 = -lw a b := by simp [omχ]

/-- **Weyl's (40)** for `ω`: `ω ≥ 0` and `ω₁ ≤ 0` on `[0, ∞)`. -/
theorem om_sign {z : ℝ} (hz : 0 ≤ z) : 0 ≤ omψ a b z ∧ omχ a b z ≤ 0 := by
  have hev : ∀ᶠ n : ℕ in atTop, z ≤ (n : ℝ) + 1 := by
    filter_upwards [eventually_ge_atTop ⌈z⌉₊] with n hn
    have h1 : z ≤ (⌈z⌉₊ : ℝ) := Nat.le_ceil z
    have h2 : (⌈z⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have t1 : Tendsto (fun n : ℕ => etaψ a b z - Lw a b (n + 1) * thψ a b z) atTop
      (𝓝 (omψ a b z)) := (h.lw_tendsto.mul_const _).const_sub _
  have t2 : Tendsto (fun n : ℕ => etaχ a b z - Lw a b (n + 1) * thχ a b z) atTop
      (𝓝 (omχ a b z)) := (h.lw_tendsto.mul_const _).const_sub _
  exact ⟨ge_of_tendsto t1 (hev.mono fun n hn => (h.comb_sign (by positivity) hz hn).1),
    le_of_tendsto t2 (hev.mono fun n hn => (h.comb_sign (by positivity) hz hn).2)⟩

/-- **Weyl's (45)**: `p ω ≤ 1`. -/
theorem omψ_le_one {z : ℝ} (hz : 0 ≤ z) : omψ a b z ≤ 1 := by
  have hm := antitoneOn_Icc_of_hasDerivAt (F := omψ a b) (s := 0) (t := z)
    (fun x h0 h1 => (h.om z).dψ x h0 h1)
    (fun x h0 _ => mul_nonpos_of_nonneg_of_nonpos (h.a0 x) (h.om_sign h0).2)
  have := hm (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
  simpa using this

/-- **Uniqueness in Weyl's auxiliary theorem**: `l` is the only constant `c` for which
`η - c ϑ` satisfies (40). -/
theorem lw_unique {c : ℝ} (h1 : ∀ z, 0 ≤ z → 0 ≤ etaψ a b z - c * thψ a b z)
    (h2 : ∀ z, 0 ≤ z → etaχ a b z - c * thχ a b z ≤ 0) : c = lw a b := by
  apply le_antisymm
  · refine le_ciInf fun n => ?_
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have := h1 _ hpos.le
    rw [Lw, le_div_iff₀ (h.thψ_pos hpos)]
    linarith
  · by_contra hlt
    push Not at hlt
    have hm : 0 < lw a b - c := sub_pos.2 hlt
    set z := 2 / (lw a b - c) with hzdef
    have hz : 0 ≤ z := by positivity
    -- `η - c ϑ` is non-increasing, hence `≤ 1`
    have hanti := antitoneOn_Icc_of_hasDerivAt (F := fun x => etaψ a b x - c * thψ a b x)
      (s := 0) (t := z)
      (fun x h0 h1' => (((h.eta z).sub_mul (h.theta z) c)).dψ x h0 h1')
      (fun x h0 _ => mul_nonpos_of_nonneg_of_nonpos (h.a0 x) (h2 x h0))
    have hle := hanti (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
    simp only [etaψ_zero, thψ_zero, mul_zero, sub_zero] at hle
    -- but it is `≥ (l - c) z = 2`
    have h3 := (h.om_sign hz).1
    have h4 := h.thψ_ge hz
    have h5 : (lw a b - c) * z = 2 := by
      rw [hzdef]
      field_simp
    have h6 : (lw a b - c) * z ≤ (lw a b - c) * thψ a b z := mul_le_mul_of_nonneg_left h4 hm.le
    simp only [omψ] at h3
    nlinarith

end Coop

end Blasius

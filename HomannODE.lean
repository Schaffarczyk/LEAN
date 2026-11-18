/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Homann's problem `λ = 1/2`: uniqueness for the differential equation (§4)

Reference: H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
Annals of Mathematics 43 (1942), 381–407, pp. 392–393.

For `λ = 1/2` the boundary-layer problem reads

  `w''' + 2 w w'' + (k² - w'²) = 0`,  `w(0) = w'(0) = 0`,  `w'(∞) = k`.

Following Weyl we differentiate once more, `w'''' + 2 w w''' = 0`, so that
`w''' = -k² e^{-2∫w}`.  Hence `w'' ` decreases; as `w'` stays bounded, `w'' ≥ 0` and
`w''(∞) = 0`.  After the scaling `g(s) = c³ w''(c s)`, `c³ w''(0) = 1`, the function `g`
solves `g = Ψ{g}` (28) and is therefore the unique fixed point `glimit` of
`HomannIteration.lean`.  This determines `w''` up to the constant `w''(0)`, which in turn is
fixed by `w'(∞) = k`.

Main result: `homann_unique` and `homann_exists_unique`.
-/
import HomannIteration

open Set Filter Topology MeasureTheory

noncomputable section

namespace Blasius

namespace Homann

/-- Solutions of `w''' + 2ww'' + (k² - w'²) = 0`, `w(0) = w'(0) = 0` on `[0, ∞)`. -/
structure IsHom (k : ℝ) (w w₁ w₂ : ℝ → ℝ) : Prop where
  d0 : ∀ z, 0 ≤ z → HasDerivWithinAt w (w₁ z) (Ici 0) z
  d1 : ∀ z, 0 ≤ z → HasDerivWithinAt w₁ (w₂ z) (Ici 0) z
  d2 : ∀ z, 0 ≤ z →
    HasDerivWithinAt w₂ (-(2 * w z * w₂ z) - (k ^ 2 - w₁ z ^ 2)) (Ici 0) z
  z0 : w 0 = 0
  z1 : w₁ 0 = 0

/-! ## General lemmas -/

lemma const_of_within {F : ℝ → ℝ} (hF : ∀ z, 0 ≤ z → HasDerivWithinAt F 0 (Ici 0) z) {z : ℝ}
    (hz : 0 ≤ z) : F z = F 0 := by
  have := eq_J_of_hasDerivWithinAt (F := fun x => F x - F 0) (p := fun _ => 0) continuous_const
    (fun x hx => (hF x hx).sub_const (F 0)) (by simp) hz
  rw [J_const] at this
  linarith

lemma J_const_mul (a : ℝ) (F : ℝ → ℝ) (z : ℝ) : J (fun t => a * F t) z = a * J F z := by
  simp [J]

lemma J_scale (a c : ℝ) (hc : c ≠ 0) (F : ℝ → ℝ) (s : ℝ) :
    J (fun t => a * F (c * t)) s = a / c * J F (c * s) := by
  rw [J_const_mul]
  unfold J
  rw [intervalIntegral.integral_comp_mul_left (fun x => F x) hc]
  simp only [mul_zero, smul_eq_mul]
  field_simp

lemma J_strict {p : ℝ → ℝ} (hp : Continuous p) (pos : ∀ t, 0 < p t) {x y : ℝ} (hxy : x < y) :
    J p x < J p y :=
  strictMono_of_deriv_pos (f := J p) (fun u => by
    rw [(J_hasDerivAt hp u).deriv]
    exact pos u) hxy

/-- A function with a limit at infinity cannot decrease at a fixed positive rate. -/
lemma unbounded_contra {F : ℝ → ℝ} {k δ z₀ : ℝ} (hδ : 0 < δ) (hF : Tendsto F atTop (𝓝 k))
    (h : ∀ z, z₀ ≤ z → F z ≤ F z₀ - δ * (z - z₀)) : False := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hF.eventually (lt_mem_nhds (show k - 1 < k by linarith)))
  set M := F z₀ - k + 1 with hM
  have h1 := h (max N z₀ + |M| / δ) (by
    have := le_max_right N z₀
    have : 0 ≤ |M| / δ := by positivity
    linarith)
  have h2 := hN (max N z₀ + |M| / δ) (by
    have := le_max_left N z₀
    have : 0 ≤ |M| / δ := by positivity
    linarith)
  have h3 : δ * (|M| / δ) = |M| := mul_div_cancel₀ _ hδ.ne'
  have h4 : δ * (max N z₀ + |M| / δ - z₀) ≥ |M| := by
    have := mul_nonneg hδ.le (sub_nonneg.2 (le_max_right N z₀))
    nlinarith
  have h5 := le_abs_self M
  linarith

/-! ## A priori properties of a solution -/

/-- `e^{-2∫w}`. -/
def ee (w : ℝ → ℝ) (z : ℝ) : ℝ := Real.exp (-(2 * J (clamp w) z))

lemma ee_pos (w : ℝ → ℝ) (z : ℝ) : 0 < ee w z := Real.exp_pos _

namespace IsHom

variable {k : ℝ} {w w₁ w₂ : ℝ → ℝ} (h : IsHom k w w₁ w₂)
include h

lemma cont0 : Continuous (clamp w) :=
  continuous_clamp fun x hx => (h.d0 x hx).continuousWithinAt

lemma cont1 : Continuous (clamp w₁) :=
  continuous_clamp fun x hx => (h.d1 x hx).continuousWithinAt

lemma cont2 : Continuous (clamp w₂) :=
  continuous_clamp fun x hx => (h.d2 x hx).continuousWithinAt

lemma ee_continuous : Continuous (ee w) := by
  have := J_continuous h.cont0
  unfold ee
  fun_prop

lemma w1_eq {z : ℝ} (hz : 0 ≤ z) : w₁ z = J (clamp w₂) z :=
  eq_J_of_hasDerivWithinAt h.cont2
    (fun x hx => by rw [clamp_of_nonneg _ hx]; exact h.d1 x hx) h.z1 hz

lemma w_eq {z : ℝ} (hz : 0 ≤ z) : w z = J (clamp w₁) z :=
  eq_J_of_hasDerivWithinAt h.cont1
    (fun x hx => by rw [clamp_of_nonneg _ hx]; exact h.d0 x hx) h.z0 hz

/-- `w'''' = -2 w w'''`. -/
lemma d3 {z : ℝ} (hz : 0 ≤ z) :
    HasDerivWithinAt (fun z => -(2 * w z * w₂ z) - (k ^ 2 - w₁ z ^ 2))
      (-(2 * w z * (-(2 * w z * w₂ z) - (k ^ 2 - w₁ z ^ 2)))) (Ici 0) z := by
  have a := ((h.d0 z hz).const_mul 2).mul (h.d2 z hz)
  have b := ((h.d1 z hz).pow 2).const_sub (k ^ 2)
  have c := a.neg.sub b
  deriv_conv c
  simp

/-- `w''' = -k² e^{-2∫w}`. -/
lemma rep3 {z : ℝ} (hz : 0 ≤ z) :
    -(2 * w z * w₂ z) - (k ^ 2 - w₁ z ^ 2) = -k ^ 2 * ee w z := by
  have hc := const_of_within
    (F := fun z => (-(2 * w z * w₂ z) - (k ^ 2 - w₁ z ^ 2)) * Real.exp (2 * J (clamp w) z))
    (fun x hx => by
      have e1 := (((J_hasDerivAt h.cont0 x).const_mul 2).exp).hasDerivWithinAt (s := Ici 0)
      have e2 := (h.d3 hx).mul e1
      deriv_conv e2
      rw [clamp_of_nonneg _ hx]
      ring) hz
  simp only [J_apply_zero, mul_zero, Real.exp_zero, mul_one, h.z0, h.z1] at hc
  have hE : Real.exp (2 * J (clamp w) z) * ee w z = 1 := by
    unfold ee
    rw [← Real.exp_add]
    simp
  have := congrArg (fun x => x * ee w z) hc
  rw [mul_assoc, hE] at this
  linarith

lemma w2_eq {z : ℝ} (hz : 0 ≤ z) : w₂ z = w₂ 0 - k ^ 2 * J (ee w) z := by
  have hp : Continuous fun x => -k ^ 2 * ee w x := h.ee_continuous.const_mul _
  have := eq_J_of_hasDerivWithinAt (F := fun x => w₂ x - w₂ 0) hp
    (fun x hx => ((h.d2 x hx).sub_const _).congr_deriv (h.rep3 hx)) (by simp) hz
  rw [J_const_mul] at this
  linarith

lemma Jee_mono {x y : ℝ} (hxy : x ≤ y) : J (ee w) x ≤ J (ee w) y := by
  rcases hxy.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (J_strict h.ee_continuous (ee_pos w) hlt).le

lemma w2_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : w₂ y ≤ w₂ x := by
  rw [h.w2_eq hx, h.w2_eq (hx.trans hxy)]
  have := h.Jee_mono hxy
  nlinarith [sq_nonneg k]

variable (hk : Tendsto w₁ atTop (𝓝 k))
include hk

lemma w2_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ w₂ z := by
  by_contra hneg
  push Not at hneg
  refine unbounded_contra (F := w₁) (z₀ := z) (δ := -w₂ z) (by linarith) hk fun y hy => ?_
  have hanti := antitoneOn_Icc_of_hasDerivAt (F := fun x => J (clamp w₂) x - w₂ z * x)
    (F' := fun x => clamp w₂ x - w₂ z) (s := z) (t := y)
    (fun x _ _ => by
      have h1 : HasDerivAt (fun x : ℝ => w₂ z * x) (w₂ z) x := by
        simpa using (hasDerivAt_id x).const_mul (w₂ z)
      exact (J_hasDerivAt h.cont2 x).sub h1)
    (fun x hx _ => by
      rw [clamp_of_nonneg _ (hz.trans hx)]
      linarith [h.w2_anti hz hx])
  have := hanti (left_mem_Icc.2 hy) (right_mem_Icc.2 hy) hy
  simp only at this
  rw [h.w1_eq hz, h.w1_eq (hz.trans hy)]
  linarith

lemma Jee_le (hk0 : 0 < k) {z : ℝ} (hz : 0 ≤ z) : J (ee w) z ≤ w₂ 0 / k ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have := h.w2_nonneg hk hz
  rw [h.w2_eq hz] at this
  linarith

lemma ee_int (hk0 : 0 < k) : IntegrableOn (ee w) (Ioi 0) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (w₂ 0 / k ^ 2) 0 (b := id)
    (l := atTop) (fun i => (h.ee_continuous.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    tendsto_id ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with i hi
  have e : (fun x => ‖ee w x‖) = ee w := funext fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (ee_pos w x)]
  rw [e]
  exact h.Jee_le hk hk0 hi

omit h hk in
lemma Jee_tendsto (hint : IntegrableOn (ee w) (Ioi 0)) :
    Tendsto (J (ee w)) atTop (𝓝 (∫ t in Ioi (0 : ℝ), ee w t)) :=
  intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id

omit hk in
lemma Jee_le_int (hint : IntegrableOn (ee w) (Ioi 0)) (z : ℝ) :
    J (ee w) z ≤ ∫ t in Ioi (0 : ℝ), ee w t :=
  ge_of_tendsto (Jee_tendsto hint) ((eventually_ge_atTop z).mono fun _ hy => h.Jee_mono hy)

/-- `w''(0) = k² ∫₀^∞ e^{-2∫w}`, i.e. `w''(∞) = 0`. -/
lemma w2_zero (hk0 : 0 < k) : w₂ 0 = k ^ 2 * ∫ t in Ioi (0 : ℝ), ee w t := by
  have hint := h.ee_int hk hk0
  have hk2 : 0 < k ^ 2 := by positivity
  have hle : (∫ t in Ioi (0 : ℝ), ee w t) ≤ w₂ 0 / k ^ 2 :=
    le_of_tendsto (Jee_tendsto hint) ((eventually_ge_atTop 0).mono fun z hz =>
      h.Jee_le hk hk0 hz)
  rw [le_div_iff₀ hk2] at hle
  by_contra hne
  have hL : 0 < w₂ 0 - k ^ 2 * ∫ t in Ioi (0 : ℝ), ee w t := by
    rcases lt_or_eq_of_le hle with hlt | heq
    · linarith
    · exact absurd (by linarith) hne
  set L := w₂ 0 - k ^ 2 * ∫ t in Ioi (0 : ℝ), ee w t with hLdef
  have hw2 : ∀ x, 0 ≤ x → L ≤ w₂ x := fun x hx => by
    rw [h.w2_eq hx]
    have := mul_le_mul_of_nonneg_left (h.Jee_le_int hint x) hk2.le
    linarith
  refine unbounded_contra (F := fun z => -w₁ z) (z₀ := 0) (δ := L) hL hk.neg fun y hy => ?_
  have hmono := monotoneOn_Icc_of_hasDerivAt (F := fun x => J (clamp w₂) x - L * x)
    (F' := fun x => clamp w₂ x - L) (s := 0) (t := y)
    (fun x _ _ => by
      have h1 : HasDerivAt (fun x : ℝ => L * x) L x := by
        simpa using (hasDerivAt_id x).const_mul L
      exact (J_hasDerivAt h.cont2 x).sub h1)
    (fun x hx _ => by
      rw [clamp_of_nonneg _ hx]
      linarith [hw2 x hx])
  have := hmono (left_mem_Icc.2 hy) (right_mem_Icc.2 hy) hy
  simp only [J_apply_zero] at this
  rw [h.z1, ← h.w1_eq hy] at *
  linarith

lemma w2_pos (hk0 : 0 < k) {z : ℝ} (hz : 0 ≤ z) : 0 < w₂ z := by
  have h1 := h.w2_nonneg hk (z := z + 1) (by linarith)
  rw [h.w2_eq (by linarith : (0 : ℝ) ≤ z + 1)] at h1
  rw [h.w2_eq hz]
  have h2 := J_strict h.ee_continuous (ee_pos w) (lt_add_one z)
  have hk2 : 0 < k ^ 2 := by positivity
  nlinarith

/-! ## Reduction to `g = Ψ{g}` -/

variable {c : ℝ}

omit hk in
lemma J_gsc (hc : 0 < c) {s : ℝ} (hs : 0 ≤ s) :
    J (fun s => c ^ 3 * clamp w₂ (c * s)) s = c ^ 2 * w₁ (c * s) := by
  rw [J_scale _ _ hc.ne', h.w1_eq (mul_nonneg hc.le hs)]
  congr 1
  field_simp

omit hk in
lemma JJ_gsc (hc : 0 < c) {s : ℝ} (hs : 0 ≤ s) :
    J (J fun s => c ^ 3 * clamp w₂ (c * s)) s = c * w (c * s) := by
  rw [J_congr (ψ := fun t => c ^ 2 * clamp w₁ (c * t)) (fun t ht => by
    rw [h.J_gsc hc ht, clamp_of_nonneg _ (mul_nonneg hc.le ht)]) hs,
    J_scale _ _ hc.ne', h.w_eq (mul_nonneg hc.le hs)]
  congr 1
  field_simp

omit hk in
lemma K_gsc (hc : 0 < c) {s : ℝ} (hs : 0 ≤ s) :
    K (fun s => c ^ 3 * clamp w₂ (c * s)) s = J (clamp w) (c * s) := by
  show J (J (J fun s => c ^ 3 * clamp w₂ (c * s))) s = _
  rw [J_congr (ψ := fun t => c * clamp w (c * t)) (fun t ht => by
    rw [h.JJ_gsc hc ht, clamp_of_nonneg _ (mul_nonneg hc.le ht)]) hs,
    J_scale _ _ hc.ne']
  field_simp

omit hk in
lemma eG_gsc (hc : 0 < c) {s : ℝ} (hs : 0 ≤ s) :
    eG (fun s => c ^ 3 * clamp w₂ (c * s)) s = ee w (c * s) := by
  unfold eG ee
  rw [h.K_gsc hc hs]

omit hk in
lemma H1_gsc (hc : 0 < c) {s : ℝ} (hs : 0 ≤ s) :
    H1 (fun s => c ^ 3 * clamp w₂ (c * s)) s = 1 / c * J (ee w) (c * s) := by
  show J (eG fun s => c ^ 3 * clamp w₂ (c * s)) s = _
  rw [J_congr (ψ := fun t => 1 * ee w (c * t)) (fun t ht => by
    rw [h.eG_gsc hc ht, one_mul]) hs, J_scale _ _ hc.ne']

omit hk in
lemma gsc_continuous : Continuous fun s => c ^ 3 * clamp w₂ (c * s) := by
  have := h.cont2
  fun_prop

lemma gsc_adm (hk0 : 0 < k) (hc : 0 < c) (hc3 : c ^ 3 * w₂ 0 = 1) :
    Adm fun s => c ^ 3 * clamp w₂ (c * s) := by
  have hc3' : 0 < c ^ 3 := by positivity
  refine adm_of_pos h.gsc_continuous (fun t ht => ?_) (fun t ht => ?_) ?_
  · rw [clamp_of_nonneg _ (mul_nonneg hc.le ht)]
    exact mul_nonneg hc3'.le (h.w2_nonneg hk (mul_nonneg hc.le ht))
  · rw [clamp_of_nonneg _ (mul_nonneg hc.le ht), ← hc3]
    exact mul_le_mul_of_nonneg_left (h.w2_anti le_rfl (mul_nonneg hc.le ht)) hc3'.le
  · refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (h.gsc_continuous.intervalIntegrable _ _) (fun x hx => ?_) one_pos
    have hx0 : 0 ≤ c * x := mul_nonneg hc.le hx.1.le
    rw [clamp_of_nonneg _ hx0]
    exact mul_pos hc3' (h.w2_pos hk hk0 hx0)

lemma Hinf_gsc (hk0 : 0 < k) (hc : 0 < c) (hc3 : c ^ 3 * w₂ 0 = 1) :
    Hinf (fun s => c ^ 3 * clamp w₂ (c * s)) = 1 / c * ∫ t in Ioi (0 : ℝ), ee w t := by
  have hint := h.ee_int hk hk0
  have t1 := (h.gsc_adm hk hk0 hc hc3).H1_tendsto
  have t2 : Tendsto (fun s => 1 / c * J (ee w) (c * s)) atTop
      (𝓝 (1 / c * ∫ t in Ioi (0 : ℝ), ee w t)) :=
    ((Jee_tendsto hint).comp (tendsto_id.const_mul_atTop hc)).const_mul _
  refine tendsto_nhds_unique (t1.congr' ?_) t2
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  exact h.H1_gsc hc hs

/-- The scaled second derivative of a solution solves `g = Ψ{g}`. -/
lemma gsc_fixed (hk0 : 0 < k) (hc : 0 < c) (hc3 : c ^ 3 * w₂ 0 = 1) {s : ℝ} (hs : 0 ≤ s) :
    psi (fun s => c ^ 3 * clamp w₂ (c * s)) s = c ^ 3 * clamp w₂ (c * s) := by
  have hcs := mul_nonneg hc.le hs
  have hE : 0 < ∫ t in Ioi (0 : ℝ), ee w t := by
    have h1 := h.w2_zero hk hk0
    have h2 := h.w2_pos hk hk0 le_rfl
    have hk2 : 0 < k ^ 2 := by positivity
    by_contra hcon
    push Not at hcon
    nlinarith
  have hz := h.w2_zero hk hk0
  unfold psi
  rw [h.H1_gsc hc hs, h.Hinf_gsc hk hk0 hc hc3, clamp_of_nonneg _ hcs, h.w2_eq hcs]
  have e1 : 1 / c * J (ee w) (c * s) / (1 / c * ∫ t in Ioi (0 : ℝ), ee w t)
      = J (ee w) (c * s) / ∫ t in Ioi (0 : ℝ), ee w t := by
    field_simp
  rw [e1]
  have e2 : c ^ 3 * (k ^ 2 * ∫ t in Ioi (0 : ℝ), ee w t) = 1 := by rw [← hz]; exact hc3
  have e3 : c ^ 3 * k ^ 2 = 1 / ∫ t in Ioi (0 : ℝ), ee w t := by
    rw [eq_div_iff hE.ne', mul_assoc]
    exact e2
  have e4 : c ^ 3 * (w₂ 0 - k ^ 2 * J (ee w) (c * s))
      = c ^ 3 * w₂ 0 - c ^ 3 * k ^ 2 * J (ee w) (c * s) := by ring
  rw [e4, hc3, e3]
  ring

/-- The second derivative of a solution is a scaled copy of the fixed point of `Ψ`. -/
lemma w2_glimit (hk0 : 0 < k) (hc : 0 < c) (hc3 : c ^ 3 * w₂ 0 = 1) {s : ℝ} (hs : 0 ≤ s) :
    c ^ 3 * w₂ (c * s) = glimit s := by
  have := psi_fixed_unique' (h.gsc_adm hk hk0 hc hc3) glimit_adm
    (fun z hz => h.gsc_fixed hk hk0 hc hc3 hz) (fun _ hz => glimit_fixed hz) hs
  simpa [clamp_of_nonneg _ (mul_nonneg hc.le hs)] using this

lemma J_glimit_tendsto (hk0 : 0 < k) (hc : 0 < c) (hc3 : c ^ 3 * w₂ 0 = 1) :
    Tendsto (J glimit) atTop (𝓝 (c ^ 2 * k)) := by
  have t : Tendsto (fun s => c ^ 2 * w₁ (c * s)) atTop (𝓝 (c ^ 2 * k)) :=
    (hk.comp (tendsto_id.const_mul_atTop hc)).const_mul _
  refine t.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  rw [← h.J_gsc hc hs]
  exact J_congr (fun t ht => by
    rw [clamp_of_nonneg _ (mul_nonneg hc.le ht)]
    exact h.w2_glimit hk hk0 hc hc3 ht) hs

end IsHom

/-- **Uniqueness for Homann's problem** (Weyl §§4–5): the boundary-value problem
`w''' + 2ww'' + (k² - w'²) = 0`, `w(0) = w'(0) = 0`, `w'(∞) = k` has at most one solution. -/
theorem homann_unique {k : ℝ} (hk0 : 0 < k) {u u₁ u₂ v v₁ v₂ : ℝ → ℝ}
    (hu : IsHom k u u₁ u₂) (hul : Tendsto u₁ atTop (𝓝 k))
    (hv : IsHom k v v₁ v₂) (hvl : Tendsto v₁ atTop (𝓝 k)) :
    ∀ z, 0 ≤ z → u z = v z ∧ u₁ z = v₁ z ∧ u₂ z = v₂ z := by
  have su := hu.w2_pos hul hk0 le_rfl
  have sv := hv.w2_pos hvl hk0 le_rfl
  obtain ⟨a, ha, ha3⟩ := exists_cube_root (inv_pos.2 su)
  obtain ⟨b, hb, hb3⟩ := exists_cube_root (inv_pos.2 sv)
  have ha3' : a ^ 3 * u₂ 0 = 1 := by rw [ha3]; exact inv_mul_cancel₀ su.ne'
  have hb3' : b ^ 3 * v₂ 0 = 1 := by rw [hb3]; exact inv_mul_cancel₀ sv.ne'
  have hab2 : a ^ 2 * k = b ^ 2 * k :=
    tendsto_nhds_unique (hu.J_glimit_tendsto hul hk0 ha ha3')
      (hv.J_glimit_tendsto hvl hk0 hb hb3')
  have hab : a = b := by
    have h2 : a ^ 2 = b ^ 2 := mul_right_cancel₀ hk0.ne' hab2
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  subst hab
  have e2 : ∀ z, 0 ≤ z → u₂ z = v₂ z := fun z hz => by
    have h1 := hu.w2_glimit hul hk0 ha ha3' (s := z / a) (by positivity)
    have h2 := hv.w2_glimit hvl hk0 ha hb3' (s := z / a) (by positivity)
    rw [mul_div_cancel₀ _ ha.ne'] at h1 h2
    have ha3p : 0 < a ^ 3 := by positivity
    exact mul_left_cancel₀ ha3p.ne' (h1.trans h2.symm)
  have e1 : ∀ z, 0 ≤ z → u₁ z = v₁ z := fun z hz => by
    rw [hu.w1_eq hz, hv.w1_eq hz]
    exact J_congr (fun t ht => by
      rw [clamp_of_nonneg _ ht, clamp_of_nonneg _ ht]
      exact e2 t ht) hz
  have e0 : ∀ z, 0 ≤ z → u z = v z := fun z hz => by
    rw [hu.w_eq hz, hv.w_eq hz]
    exact J_congr (fun t ht => by
      rw [clamp_of_nonneg _ ht, clamp_of_nonneg _ ht]
      exact e1 t ht) hz
  exact fun z hz => ⟨e0 z hz, e1 z hz, e2 z hz⟩

/-- **Homann's problem is uniquely solvable**: for every `k > 0` there is exactly one
solution of `w''' + 2ww'' + (k² - w'²) = 0`, `w(0) = w'(0) = 0`, `w'(∞) = k` on `[0, ∞)`.
Existence is `weyl_Alam_exists` with `λ = 1/2`. -/
theorem homann_exists_unique {k : ℝ} (hk0 : 0 < k) :
    ∃ w w₁ w₂ : ℝ → ℝ, (IsHom k w w₁ w₂ ∧ Tendsto w₁ atTop (𝓝 k)) ∧
      ∀ v v₁ v₂ : ℝ → ℝ, IsHom k v v₁ v₂ → Tendsto v₁ atTop (𝓝 k) →
        ∀ z, 0 ≤ z → v z = w z ∧ v₁ z = w₁ z ∧ v₂ z = w₂ z := by
  obtain ⟨w, w₁, w₂, d0, d1, d2, z0, z1, hl⟩ :=
    weyl_Alam_exists (lam := 1 / 2) (by norm_num) k hk0
  have hw : IsHom k w w₁ w₂ :=
    ⟨fun z _ => (d0 z).hasDerivWithinAt, fun z _ => (d1 z).hasDerivWithinAt,
      fun z hz => (d2 z hz).congr_deriv (by ring), z0, z1⟩
  exact ⟨w, w₁, w₂, ⟨hw, hl⟩, fun v v₁ v₂ hv hvl => homann_unique hk0 hv hvl hw hl⟩

end Homann

end Blasius

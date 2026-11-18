/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Homann's problem `λ = 1/2`: the operator `Ψ` (§4)

Reference: H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
Annals of Mathematics 43 (1942), 381–407, pp. 392–396.

For `λ = 1/2` the function `g = f''` of the normalised solution satisfies `g = Ψ{g}`,

  `Ψ{g}(z) = ∫_z^∞ e^{-G} / ∫_0^∞ e^{-G}`,   `G(z) = ∫₀ᶻ (z - ζ)² g(ζ) dζ = 2 J³ g`      (28).

* `psi_antitone`: `Ψ{g} ≥ Ψ{g*}` if `g ≤ g*` (Weyl's (29));
* `psi_sub_le`: `0 ≤ Ψ{g} - Ψ{g*} ≤ q(g) · μ` if `0 ≤ g* - g ≤ μ`, where
  `q(g) = ∫ e^{-G} z³/3 / ∫ e^{-G}` (p. 395);
* `J_psi_sq`, `qq_antitone`: `q(g) = ∫₀^∞ Ψ{g} z² dz`, hence `q` is antitone and all the
  constants `qₙ` of Weyl's iteration are bounded by `q₂ = q(g₂)`, `g₂ = Ψ{1}`;
* `psi_fixed_unique`: if `q₂ < 1`, the equation `g = Ψ{g}` has at most one solution with
  `g₂ ≤ g ≤ 1`.  (For non-comparable `u, v` one compares both with `min u v`.)

The inequality `q₂ < 1` is Weyl's §5 and is proved in `HomannNumerics.lean`.
-/
import WeylMain

open Set Filter Topology MeasureTheory

noncomputable section

namespace Blasius

namespace Homann

/-- `e^{-G}` with `G = 2 J³ g`. -/
def eG (g : ℝ → ℝ) (z : ℝ) : ℝ := Real.exp (-(2 * K g z))

/-- Weyl's `H₁(z) = ∫₀ᶻ e^{-G}`. -/
def H1 (g : ℝ → ℝ) : ℝ → ℝ := J (eG g)

/-- Weyl's `H = ∫₀^∞ e^{-G}`. -/
def Hinf (g : ℝ → ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), eG g t

/-- `∫₀^∞ e^{-G} z³/3 dz`. -/
def N3 (g : ℝ → ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), eG g t * (t ^ 3 / 3)

/-- `∫₀ᴿ e^{-G} z³/3 dz`. -/
def NR (g : ℝ → ℝ) : ℝ → ℝ := J (fun t => eG g t * (t ^ 3 / 3))

/-- Weyl's operator `Ψ{g} = H₂ / (H₁ + H₂) = 1 - H₁ / H` (28). -/
def psi (g : ℝ → ℝ) (z : ℝ) : ℝ := 1 - H1 g z / Hinf g

/-- `Ψ{g}` with the argument clamped at `0`. -/
def Psi (g : ℝ → ℝ) (z : ℝ) : ℝ := psi g (max z 0)

/-- Weyl's quotient `q = ∫ e^{-G} z³/3 / ∫ e^{-G}`. -/
def qq (g : ℝ → ℝ) : ℝ := N3 g / Hinf g

/-- Functions to which `Ψ` is applicable. -/
structure Adm (g : ℝ → ℝ) : Prop where
  cont : Continuous g
  le_one : ∀ t, 0 ≤ t → g t ≤ 1
  int0 : IntegrableOn (eG g) (Ioi 0)
  int3 : IntegrableOn (fun t => eG g t * (t ^ 3 / 3)) (Ioi 0)

lemma eG_pos (g : ℝ → ℝ) (z : ℝ) : 0 < eG g z := Real.exp_pos _

lemma eG_continuous {g : ℝ → ℝ} (hg : Continuous g) : Continuous (eG g) := by
  have := K_continuous hg
  unfold eG
  fun_prop

lemma hasDerivAt_K {g : ℝ → ℝ} (hg : Continuous g) (z : ℝ) : HasDerivAt (K g) (J (J g) z) z :=
  J_hasDerivAt (J_continuous (J_continuous hg)) z

lemma hasDerivAt_H1 {g : ℝ → ℝ} (hg : Continuous g) (z : ℝ) : HasDerivAt (H1 g) (eG g z) z :=
  J_hasDerivAt (eG_continuous hg) z

lemma eG3_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous fun t => eG g t * (t ^ 3 / 3) := by
  have := eG_continuous hg
  fun_prop

lemma hasDerivAt_NR {g : ℝ → ℝ} (hg : Continuous g) (z : ℝ) :
    HasDerivAt (NR g) (eG g z * (z ^ 3 / 3)) z :=
  J_hasDerivAt (eG3_continuous hg) z

lemma K_const (μ t : ℝ) : K (fun _ => μ) t = μ * t ^ 3 / 6 := by
  have e : (fun _ : ℝ => μ) = fun t => μ * t ^ 0 := by
    funext t
    simp
  rw [e, K_monomial]
  norm_num
  ring

/-! ## Basic properties -/

namespace Adm

variable {g : ℝ → ℝ} (hg : Adm g)
include hg

lemma H1_tendsto : Tendsto (H1 g) atTop (𝓝 (Hinf g)) :=
  intervalIntegral_tendsto_integral_Ioi 0 hg.int0 tendsto_id

lemma NR_tendsto : Tendsto (NR g) atTop (𝓝 (N3 g)) :=
  intervalIntegral_tendsto_integral_Ioi 0 hg.int3 tendsto_id

lemma H1_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : H1 g x ≤ H1 g y := by
  have hm := monotoneOn_Icc_of_hasDerivAt (F := H1 g) (s := 0) (t := y)
    (fun u _ _ => hasDerivAt_H1 hg.cont u) (fun u _ _ => (eG_pos g u).le)
  exact hm ⟨hx, hxy⟩ (right_mem_Icc.2 (hx.trans hxy)) hxy

lemma H1_le {z : ℝ} (hz : 0 ≤ z) : H1 g z ≤ Hinf g :=
  ge_of_tendsto hg.H1_tendsto ((eventually_ge_atTop z).mono fun _ hy => hg.H1_mono hz hy)

omit hg in
lemma H1_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ H1 g z :=
  J_nonneg (fun t _ => (eG_pos g t).le) hz

lemma H1_pos {z : ℝ} (hz : 0 < z) : 0 < H1 g z :=
  intervalIntegral.intervalIntegral_pos_of_pos_on ((eG_continuous hg.cont).intervalIntegrable _ _)
    (fun x _ => eG_pos g x) hz

lemma Hinf_pos : 0 < Hinf g := lt_of_lt_of_le (hg.H1_pos one_pos) (hg.H1_le zero_le_one)

lemma H1_lt {z : ℝ} (hz : 0 ≤ z) : H1 g z < Hinf g := by
  have h1 : H1 g z < H1 g (z + 1) := by
    have hd : ∀ u, HasDerivAt (fun y => H1 g y - H1 g z) (eG g u) u := fun u =>
      (hasDerivAt_H1 hg.cont u).sub_const _
    have hs : StrictMono fun y => H1 g y - H1 g z :=
      strictMono_of_deriv_pos fun u => by
        rw [(hd u).deriv]
        exact eG_pos g u
    have := hs (lt_add_one z)
    simp only [sub_self] at this
    linarith
  exact lt_of_lt_of_le h1 (hg.H1_le (by linarith))

lemma psi_mem {z : ℝ} (hz : 0 ≤ z) : 0 ≤ psi g z ∧ psi g z ≤ 1 := by
  have hH := hg.Hinf_pos
  have h1 := H1_nonneg (g := g) hz
  have h2 := hg.H1_le hz
  have h3 : H1 g z / Hinf g ≤ 1 := (div_le_one hH).2 h2
  have h4 : 0 ≤ H1 g z / Hinf g := div_nonneg h1 hH.le
  unfold psi
  exact ⟨by linarith, by linarith⟩

lemma psi_pos {z : ℝ} (hz : 0 ≤ z) : 0 < psi g z := by
  have hH := hg.Hinf_pos
  have h3 : H1 g z / Hinf g < 1 := (div_lt_one hH).2 (hg.H1_lt hz)
  unfold psi
  linarith

lemma hasDerivAt_psi (z : ℝ) : HasDerivAt (psi g) (-(eG g z / Hinf g)) z := by
  have := ((hasDerivAt_H1 hg.cont z).div_const (Hinf g)).const_sub 1
  exact this

lemma psi_continuous : Continuous (psi g) :=
  continuous_iff_continuousAt.2 fun z => (hg.hasDerivAt_psi z).continuousAt

lemma Psi_continuous : Continuous (Psi g) :=
  hg.psi_continuous.comp (continuous_id.max continuous_const)

omit hg in
lemma Psi_eq {z : ℝ} (hz : 0 ≤ z) : Psi g z = psi g z := by rw [Psi, max_eq_left hz]

omit hg in
lemma N3_nonneg : 0 ≤ N3 g :=
  setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have := eG_pos g t
    have : (0 : ℝ) ≤ t ^ 3 / 3 := by
      have ht' : (0 : ℝ) < t := ht
      positivity
    positivity

lemma qq_nonneg : 0 ≤ qq g := div_nonneg N3_nonneg hg.Hinf_pos.le

/-- `Ψ` is applicable to every continuous `v` with `g ≤ v ≤ 1`. -/
lemma of_le {v : ℝ → ℝ} (hv : Continuous v) (hgv : ∀ t, 0 ≤ t → g t ≤ v t)
    (hv1 : ∀ t, 0 ≤ t → v t ≤ 1) : Adm v := by
  have hle : ∀ t, 0 ≤ t → eG v t ≤ eG g t := fun t ht => by
    unfold eG
    rw [Real.exp_le_exp]
    linarith [K_mono hg.cont hv hgv ht]
  refine ⟨hv, hv1, ?_, ?_⟩
  · refine Integrable.mono' hg.int0 (eG_continuous hv).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (eG_pos v t)]
    exact hle t (le_of_lt ht)
  · refine Integrable.mono' hg.int3 (eG3_continuous hv).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    have h3 : (0 : ℝ) ≤ t ^ 3 / 3 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (eG_pos v t).le h3)]
    exact mul_le_mul_of_nonneg_right (hle t ht'.le) h3

end Adm

/-! ## Monotonicity of `Ψ` (Weyl's (29)) -/

section Compare

variable {u v : ℝ → ℝ}

/-- `ΔG = G* - G` is non-decreasing on `[0, ∞)` when `g ≤ g*`. -/
lemma dG_mono (hu : Continuous u) (hv : Continuous v) (huv : ∀ t, 0 ≤ t → u t ≤ v t)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    2 * K v x - 2 * K u x ≤ 2 * K v y - 2 * K u y := by
  have hm := monotoneOn_Icc_of_hasDerivAt (F := fun z => 2 * K v z - 2 * K u z)
    (F' := fun z => 2 * J (J v) z - 2 * J (J u) z) (s := 0) (t := y)
    (fun z _ _ => ((hasDerivAt_K hv z).const_mul 2).sub ((hasDerivAt_K hu z).const_mul 2))
    (fun z hz _ => by
      have := J_mono (J_continuous hu) (J_continuous hv) (fun t ht => J_mono hu hv huv ht) hz
      linarith)
  exact hm ⟨hx, hxy⟩ (right_mem_Icc.2 (hx.trans hxy)) hxy

lemma eG_eq (u v : ℝ → ℝ) (t : ℝ) :
    eG v t = eG u t * Real.exp (-(2 * K v t - 2 * K u t)) := by
  unfold eG
  rw [← Real.exp_add]
  congr 1
  ring

lemma H1_ge (hu : Continuous u) (hv : Continuous v) (huv : ∀ t, 0 ≤ t → u t ≤ v t) {z : ℝ}
    (hz : 0 ≤ z) : Real.exp (-(2 * K v z - 2 * K u z)) * H1 u z ≤ H1 v z := by
  set c := Real.exp (-(2 * K v z - 2 * K u z)) with hc
  have hm := monotoneOn_Icc_of_hasDerivAt (F := fun y => H1 v y - c * H1 u y)
    (F' := fun y => eG v y - c * eG u y) (s := 0) (t := z)
    (fun y _ _ => (hasDerivAt_H1 hv y).sub ((hasDerivAt_H1 hu y).const_mul c))
    (fun y hy0 hyz => by
      rw [eG_eq u v y]
      have h1 : c ≤ Real.exp (-(2 * K v y - 2 * K u y)) := by
        rw [hc, Real.exp_le_exp]
        linarith [dG_mono hu hv huv hy0 hyz]
      have := mul_le_mul_of_nonneg_left h1 (eG_pos u y).le
      linarith)
  have := hm (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
  simp only [H1, J_apply_zero, mul_zero, sub_zero] at this
  simp only [H1]
  linarith

lemma tail_le (hu : Adm u) (hv : Adm v) (huv : ∀ t, 0 ≤ t → u t ≤ v t) {z : ℝ} (hz : 0 ≤ z) :
    Hinf v - H1 v z ≤ Real.exp (-(2 * K v z - 2 * K u z)) * (Hinf u - H1 u z) := by
  set c := Real.exp (-(2 * K v z - 2 * K u z)) with hc
  have key : ∀ y, z ≤ y → H1 v y - H1 v z ≤ c * (H1 u y - H1 u z) := by
    intro y hy
    have hm := monotoneOn_Icc_of_hasDerivAt (F := fun x => c * H1 u x - H1 v x)
      (F' := fun x => c * eG u x - eG v x) (s := z) (t := y)
      (fun x _ _ => ((hasDerivAt_H1 hu.cont x).const_mul c).sub (hasDerivAt_H1 hv.cont x))
      (fun x hx _ => by
        rw [eG_eq u v x]
        have h1 : Real.exp (-(2 * K v x - 2 * K u x)) ≤ c := by
          rw [hc, Real.exp_le_exp]
          linarith [dG_mono hu.cont hv.cont huv hz hx]
        have := mul_le_mul_of_nonneg_left h1 (eG_pos u x).le
        linarith)
    have := hm (left_mem_Icc.2 hy) (right_mem_Icc.2 hy) hy
    simp only at this
    linarith
  exact le_of_tendsto_of_tendsto (hv.H1_tendsto.sub_const _)
    ((hu.H1_tendsto.sub_const _).const_mul c) ((eventually_ge_atTop z).mono fun y hy => key y hy)

/-- **Weyl's (29)**: `Ψ{g*} ≤ Ψ{g}` if `g ≤ g*`. -/
theorem psi_antitone (hu : Adm u) (hv : Adm v) (huv : ∀ t, 0 ≤ t → u t ≤ v t) {z : ℝ}
    (hz : 0 ≤ z) : psi v z ≤ psi u z := by
  have hHu := hu.Hinf_pos
  have hHv := hv.Hinf_pos
  have hA := H1_ge hu.cont hv.cont huv hz
  have hB := tail_le hu hv huv hz
  have hc := Real.exp_pos (-(2 * K v z - 2 * K u z))
  have ha := Adm.H1_nonneg (g := u) hz
  have hTu : 0 ≤ Hinf u - H1 u z := sub_nonneg.2 (hu.H1_le hz)
  have hTv : 0 ≤ Hinf v - H1 v z := sub_nonneg.2 (hv.H1_le hz)
  have key : H1 u z / Hinf u ≤ H1 v z / Hinf v := by
    rw [div_le_div_iff₀ hHu hHv]
    have h1 := mul_le_mul_of_nonneg_left hB ha
    have h2 := mul_le_mul_of_nonneg_right hA hTu
    nlinarith
  unfold psi
  linarith

/-- **The contraction estimate** (p. 394–395): `Ψ{g} - Ψ{g*} ≤ q(g) μ` if `0 ≤ g* - g ≤ μ`. -/
theorem psi_sub_le (hu : Adm u) (hv : Adm v) (huv : ∀ t, 0 ≤ t → u t ≤ v t) {μ : ℝ}
    (hμ : ∀ t, 0 ≤ t → v t - u t ≤ μ) {z : ℝ} (hz : 0 ≤ z) :
    psi u z - psi v z ≤ qq u * μ := by
  have hHu := hu.Hinf_pos
  have hHv := hv.Hinf_pos
  have hle : ∀ t, 0 ≤ t → eG v t ≤ eG u t := fun t ht => by
    unfold eG
    rw [Real.exp_le_exp]
    linarith [K_mono hu.cont hv.cont huv ht]
  -- `H₁* ≤ H₁`, `H* ≤ H`
  have hba : H1 v z ≤ H1 u z := J_mono (eG_continuous hv.cont) (eG_continuous hu.cont) hle hz
  have hHvu : Hinf v ≤ Hinf u :=
    setIntegral_mono_on hv.int0 hu.int0 measurableSet_Ioi fun t ht => hle t (le_of_lt ht)
  have hbH := hv.H1_le hz
  -- `Ψ{g} - Ψ{g*} ≤ (H - H*) / H`
  have step1 : psi u z - psi v z ≤ (Hinf u - Hinf v) / Hinf u := by
    have e : psi u z - psi v z = H1 v z / Hinf v - H1 u z / Hinf u := by
      unfold psi
      ring
    rw [e, div_sub_div _ _ hHv.ne' hHu.ne', div_le_div_iff₀ (mul_pos hHv hHu) hHu]
    have h1 : H1 v z * Hinf u - Hinf v * H1 u z ≤ (Hinf u - Hinf v) * Hinf v := by
      nlinarith [mul_nonneg (sub_nonneg.2 hHvu) (sub_nonneg.2 hbH),
        mul_le_mul_of_nonneg_left hba hHv.le]
    calc (H1 v z * Hinf u - Hinf v * H1 u z) * Hinf u
        ≤ (Hinf u - Hinf v) * Hinf v * Hinf u := mul_le_mul_of_nonneg_right h1 hHu.le
      _ = (Hinf u - Hinf v) * (Hinf v * Hinf u) := by ring
  -- `H - H* ≤ μ ∫ e^{-G} z³/3`
  have step2 : Hinf u - Hinf v ≤ μ * N3 u := by
    have e1 : Hinf u - Hinf v = ∫ t in Ioi (0 : ℝ), (eG u t - eG v t) :=
      (integral_sub hu.int0 hv.int0).symm
    have e2 : μ * N3 u = ∫ t in Ioi (0 : ℝ), μ * (eG u t * (t ^ 3 / 3)) :=
      (integral_const_mul μ _).symm
    rw [e1, e2]
    refine setIntegral_mono_on (hu.int0.sub hv.int0) (hu.int3.const_mul μ) measurableSet_Ioi
      fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have hD : 2 * K v t - 2 * K u t ≤ μ * t ^ 3 / 3 := by
      have := K_sub_le hv.cont hu.cont (d := fun _ => μ) continuous_const
        (fun s hs => by
          rw [abs_of_nonneg (by linarith [huv s hs])]
          exact hμ s hs) ht0
      rw [K_const] at this
      have := (abs_le.1 this).2
      linarith
    have h1 : 1 - Real.exp (-(2 * K v t - 2 * K u t)) ≤ 2 * K v t - 2 * K u t := by
      linarith [Real.add_one_le_exp (-(2 * K v t - 2 * K u t))]
    rw [eG_eq u v t]
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hD) (eG_pos u t).le
    linarith
  have step3 : (Hinf u - Hinf v) / Hinf u ≤ qq u * μ := by
    unfold qq
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hHu]
    linarith
  exact step1.trans step3

end Compare

/-! ## The second expression `q = ∫₀^∞ Ψ{g} z² dz` and the monotonicity of `q` -/

namespace Adm

variable {g : ℝ → ℝ} (hg : Adm g)
include hg

/-- Partial integration: `∫₀ᴿ Ψ{g} z² dz = (∫₀ᴿ e^{-G} z³/3) / H + Ψ{g}(R) R³/3`. -/
lemma J_psi_sq {R : ℝ} (hR : 0 ≤ R) :
    J (fun t => psi g t * t ^ 2) R = NR g R / Hinf g + psi g R * (R ^ 3 / 3) := by
  have hc : Continuous fun t => psi g t * t ^ 2 := by
    have := hg.psi_continuous
    fun_prop
  have := eq_of_hasDerivAt_zero
    (F := fun z => J (fun t => psi g t * t ^ 2) z - NR g z / Hinf g - psi g z * (z ^ 3 / 3)) hR
    (fun z _ _ => by
      have h1 := J_hasDerivAt hc z
      have h2 := (hasDerivAt_NR hg.cont z).div_const (Hinf g)
      have h3 : HasDerivAt (fun z : ℝ => z ^ 3 / 3) (z ^ 2) z := by
        have := ((hasDerivAt_id z).pow 3).div_const 3
        deriv_conv this
        simp
      have h4 := (hg.hasDerivAt_psi z).mul h3
      have h5 := (h1.sub h2).sub h4
      deriv_conv h5
      ring)
  simp only [J_apply_zero, NR, zero_div, sub_zero] at this
  simp only [NR]
  norm_num at this
  linarith

lemma tail3 {R : ℝ} (hR : 0 ≤ R) : R ^ 3 / 3 * (Hinf g - H1 g R) ≤ N3 g - NR g R := by
  have key : ∀ y, R ≤ y → R ^ 3 / 3 * (H1 g y - H1 g R) ≤ NR g y - NR g R := by
    intro y hy
    have hm := monotoneOn_Icc_of_hasDerivAt (F := fun x => NR g x - R ^ 3 / 3 * H1 g x)
      (F' := fun x => eG g x * (x ^ 3 / 3) - R ^ 3 / 3 * eG g x) (s := R) (t := y)
      (fun x _ _ => (hasDerivAt_NR hg.cont x).sub ((hasDerivAt_H1 hg.cont x).const_mul _))
      (fun x hx _ => by
        have h1 : R ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hR hx 3
        have h2 := eG_pos g x
        nlinarith)
    have := hm (left_mem_Icc.2 hy) (right_mem_Icc.2 hy) hy
    simp only at this
    linarith
  exact le_of_tendsto_of_tendsto ((hg.H1_tendsto.sub_const _).const_mul _)
    (hg.NR_tendsto.sub_const _) ((eventually_ge_atTop R).mono fun y hy => key y hy)

lemma NR_div_le {R : ℝ} (hR : 0 ≤ R) : NR g R / Hinf g ≤ J (fun t => psi g t * t ^ 2) R := by
  rw [hg.J_psi_sq hR]
  have h1 := (hg.psi_mem hR).1
  have : (0 : ℝ) ≤ R ^ 3 / 3 := by positivity
  nlinarith

lemma J_psi_sq_le {R : ℝ} (hR : 0 ≤ R) : J (fun t => psi g t * t ^ 2) R ≤ qq g := by
  have hH := hg.Hinf_pos
  rw [hg.J_psi_sq hR]
  have h1 := hg.tail3 hR
  have e : NR g R / Hinf g + psi g R * (R ^ 3 / 3)
      = (NR g R + R ^ 3 / 3 * (Hinf g - H1 g R)) / Hinf g := by
    unfold psi
    field_simp
  rw [e, qq, div_le_div_iff_of_pos_right hH]
  linarith

end Adm

/-- `q` is antitone: `q(g*) ≤ q(g)` if `g ≤ g*`. -/
theorem qq_antitone {u v : ℝ → ℝ} (hu : Adm u) (hv : Adm v) (huv : ∀ t, 0 ≤ t → u t ≤ v t) :
    qq v ≤ qq u := by
  have hcu : Continuous fun t => psi u t * t ^ 2 := by
    have := hu.psi_continuous
    fun_prop
  have hcv : Continuous fun t => psi v t * t ^ 2 := by
    have := hv.psi_continuous
    fun_prop
  have key : ∀ R, 0 ≤ R → NR v R / Hinf v ≤ qq u := fun R hR =>
    (hv.NR_div_le hR).trans
      ((J_mono hcv hcu (fun t ht =>
        mul_le_mul_of_nonneg_right (psi_antitone hu hv huv ht) (sq_nonneg t)) hR).trans
        (hu.J_psi_sq_le hR))
  exact le_of_tendsto (hv.NR_tendsto.div_const _) ((eventually_ge_atTop 0).mono key)

/-! ## Applicability of `Ψ`: Gaussian decay of `e^{-G}` -/

lemma cube_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 3 ≤ 27 * Real.exp x := by
  have h1 : x / 3 ≤ Real.exp (x / 3) := by linarith [Real.add_one_le_exp (x / 3)]
  have h2 : (x / 3) ^ 3 ≤ Real.exp (x / 3) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  have h3 : Real.exp (x / 3) ^ 3 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h3] at h2
  have : (x / 3) ^ 3 = x ^ 3 / 27 := by ring
  linarith

/-- If `g ≥ 0`, `g ≤ 1` and `∫₀¹ g > 0`, then `Ψ` is applicable to `g`. -/
theorem adm_of_pos {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ t, 0 ≤ t → 0 ≤ g t)
    (hg1 : ∀ t, 0 ≤ t → g t ≤ 1) (hm : 0 < J g 1) : Adm g := by
  set m := J g 1 with hmdef
  -- `J g ≥ m`, `J² g ≥ m (z - 1)`, `K g ≥ m (z - 1)² / 2` for `z ≥ 1`
  have b1 : ∀ z, 1 ≤ z → m ≤ J g z := fun z hz => by
    have hmo := monotoneOn_Icc_of_hasDerivAt (F := J g) (s := 0) (t := z)
      (fun u _ _ => J_hasDerivAt hg u) (fun u hu _ => hg0 u hu)
    exact hmo ⟨zero_le_one, hz⟩ (right_mem_Icc.2 (zero_le_one.trans hz)) hz
  have b2 : ∀ z, 1 ≤ z → m * (z - 1) ≤ J (J g) z := fun z hz => by
    have hmo := monotoneOn_Icc_of_hasDerivAt (F := fun x => J (J g) x - m * (x - 1))
      (F' := fun x => J g x - m) (s := 1) (t := z)
      (fun x _ _ => by
        have h1 : HasDerivAt (fun x : ℝ => m * (x - 1)) m x := by
          have := ((hasDerivAt_id x).sub_const 1).const_mul m
          deriv_conv this
          simp
        exact (J_hasDerivAt (J_continuous hg) x).sub h1)
      (fun x hx _ => sub_nonneg.2 (b1 x hx))
    have := hmo (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
    simp only [sub_self, mul_zero, sub_zero] at this
    have h0 : 0 ≤ J (J g) 1 := J_nonneg (fun t ht => J_nonneg hg0 ht) zero_le_one
    linarith
  have b3 : ∀ z, 1 ≤ z → m * (z - 1) ^ 2 / 2 ≤ K g z := fun z hz => by
    have hmo := monotoneOn_Icc_of_hasDerivAt (F := fun x => K g x - m * (x - 1) ^ 2 / 2)
      (F' := fun x => J (J g) x - m * (x - 1)) (s := 1) (t := z)
      (fun x _ _ => by
        have h1 : HasDerivAt (fun x : ℝ => m * (x - 1) ^ 2 / 2) (m * (x - 1)) x := by
          have := ((((hasDerivAt_id x).sub_const 1).pow 2).const_mul m).div_const 2
          deriv_conv this
          simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
          ring
        exact (hasDerivAt_K hg x).sub h1)
      (fun x hx _ => sub_nonneg.2 (b2 x hx))
    have := hmo (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
    simp only [sub_self] at this
    have h0 : 0 ≤ K g 1 := K_nonneg hg0 zero_le_one
    nlinarith
  -- `e^{-G} ≤ e^{8m} e^{-4 m z}` on `[0, ∞)`
  have hbound : ∀ z, 0 ≤ z → eG g z ≤ Real.exp (8 * m) * Real.exp (-(4 * m) * z) := by
    intro z hz
    rw [← Real.exp_add]
    unfold eG
    rw [Real.exp_le_exp]
    rcases le_total 1 z with h1 | h1
    · have := b3 z h1
      nlinarith [sq_nonneg (z - 3)]
    · have := K_nonneg hg0 hz
      nlinarith
  have h4m : 0 < 4 * m := by positivity
  refine ⟨hg, hg1, ?_, ?_⟩
  · refine integrable_of_isBigO_exp_neg h4m (eG_continuous hg).continuousOn ?_
    refine Asymptotics.IsBigO.of_bound (Real.exp (8 * m)) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (eG_pos g x), Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact hbound x hx
  · refine integrable_of_isBigO_exp_neg hm (eG3_continuous hg).continuousOn ?_
    refine Asymptotics.IsBigO.of_bound (Real.exp (8 * m) * (9 / m ^ 3)) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have h3 : (0 : ℝ) ≤ x ^ 3 / 3 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (eG_pos g x).le h3), Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hc := cube_le_exp (mul_nonneg hm.le hx)
    have hx3 : x ^ 3 ≤ 27 / m ^ 3 * Real.exp (m * x) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      calc x ^ 3 * m ^ 3 = (m * x) ^ 3 := by ring
        _ ≤ 27 * Real.exp (m * x) := hc
    have hE : Real.exp (-(4 * m) * x) * Real.exp (m * x) ≤ Real.exp (-m * x) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith
    have hb := hbound x hx
    have hE8 := Real.exp_pos (8 * m)
    have hE4 := Real.exp_pos (-(4 * m) * x)
    have hm3 : 0 < m ^ 3 := by positivity
    calc eG g x * (x ^ 3 / 3)
        ≤ Real.exp (8 * m) * Real.exp (-(4 * m) * x) * (27 / m ^ 3 * Real.exp (m * x) / 3) := by
          apply mul_le_mul hb _ h3 (by positivity)
          exact div_le_div_of_nonneg_right hx3 (by norm_num)
      _ = Real.exp (8 * m) * (9 / m ^ 3) * (Real.exp (-(4 * m) * x) * Real.exp (m * x)) := by
          ring
      _ ≤ Real.exp (8 * m) * (9 / m ^ 3) * Real.exp (-m * x) :=
          mul_le_mul_of_nonneg_left hE (by positivity)

/-! ## The iteration and uniqueness of the fixed point -/

lemma adm_one : Adm fun _ => (1 : ℝ) :=
  adm_of_pos continuous_const (fun _ _ => zero_le_one) (fun _ _ => le_rfl)
    (by rw [J_const]; norm_num)

/-- Weyl's `g₂ = Ψ{1}`. -/
def g2 : ℝ → ℝ := Psi fun _ => 1

lemma g2_continuous : Continuous g2 := adm_one.Psi_continuous

lemma g2_mem (t : ℝ) : 0 < g2 t ∧ g2 t ≤ 1 :=
  ⟨adm_one.psi_pos (le_max_right t 0), (adm_one.psi_mem (le_max_right t 0)).2⟩

lemma adm_g2 : Adm g2 :=
  adm_of_pos g2_continuous (fun t _ => (g2_mem t).1.le) (fun t _ => (g2_mem t).2)
    (intervalIntegral.intervalIntegral_pos_of_pos_on (g2_continuous.intervalIntegrable _ _)
      (fun x _ => (g2_mem x).1) one_pos)

/-- Every continuous `g` with `g₂ ≤ g ≤ 1` is admissible. -/
lemma adm_of_between {g : ℝ → ℝ} (hg : Continuous g) (h2 : ∀ t, 0 ≤ t → g2 t ≤ g t)
    (h1 : ∀ t, 0 ≤ t → g t ≤ 1) : Adm g := adm_g2.of_le hg h2 h1

/-- Weyl's constant `q₂`. -/
def q2 : ℝ := qq g2

/-- **Uniqueness of the solution of `g = Ψ{g}`** between `g₂` and `1`, provided `q₂ < 1`
(Weyl, p. 396). -/
theorem psi_fixed_unique (hq : q2 < 1) {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu2 : ∀ t, 0 ≤ t → g2 t ≤ u t) (hu1 : ∀ t, 0 ≤ t → u t ≤ 1)
    (hv2 : ∀ t, 0 ≤ t → g2 t ≤ v t) (hv1 : ∀ t, 0 ≤ t → v t ≤ 1)
    (fu : ∀ z, 0 ≤ z → psi u z = u z) (fv : ∀ z, 0 ≤ z → psi v z = v z) {z : ℝ} (hz : 0 ≤ z) :
    u z = v z := by
  have hq0 : 0 ≤ q2 := adm_g2.qq_nonneg
  have au := adm_of_between hu hu2 hu1
  have av := adm_of_between hv hv2 hv1
  -- the lower envelope
  have hw : Continuous fun t => min (u t) (v t) := hu.min hv
  have aw : Adm fun t => min (u t) (v t) :=
    adm_of_between hw (fun t ht => le_min (hu2 t ht) (hv2 t ht))
      (fun t ht => (min_le_left _ _).trans (hu1 t ht))
  have hqw : qq (fun t => min (u t) (v t)) ≤ q2 :=
    qq_antitone adm_g2 aw fun t ht => le_min (hu2 t ht) (hv2 t ht)
  have key : ∀ (n : ℕ) (t : ℝ), 0 ≤ t → |u t - v t| ≤ q2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have a1 := (g2_mem t).1.le.trans (hu2 t ht)
      have a2 := (g2_mem t).1.le.trans (hv2 t ht)
      rw [pow_zero, abs_le]
      constructor <;> linarith [hu1 t ht, hv1 t ht]
    | succ n ih =>
      intro t ht
      have hμu : ∀ s, 0 ≤ s → u s - min (u s) (v s) ≤ q2 ^ n := fun s hs => by
        rcases le_total (u s) (v s) with h | h
        · rw [min_eq_left h, sub_self]
          positivity
        · rw [min_eq_right h]
          exact (le_abs_self _).trans (ih s hs)
      have hμv : ∀ s, 0 ≤ s → v s - min (u s) (v s) ≤ q2 ^ n := fun s hs => by
        rcases le_total (u s) (v s) with h | h
        · rw [min_eq_left h]
          exact (neg_le_abs _).trans' (by linarith) |>.trans (ih s hs)
        · rw [min_eq_right h, sub_self]
          positivity
      have c1 := psi_sub_le aw au (fun s _ => min_le_left _ _) hμu ht
      have c2 := psi_sub_le aw av (fun s _ => min_le_right _ _) hμv ht
      have d1 := psi_antitone aw au (fun s _ => min_le_left _ _) ht
      have d2 := psi_antitone aw av (fun s _ => min_le_right _ _) ht
      have hqn : qq (fun t => min (u t) (v t)) * q2 ^ n ≤ q2 ^ (n + 1) := by
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_right hqw (by positivity)
      rw [← fu t ht, ← fv t ht, abs_le]
      constructor <;> linarith
  have hlim : Tendsto (fun n : ℕ => q2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq
  have h0 := ge_of_tendsto' hlim fun n => key n z hz
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

end Homann

end Blasius

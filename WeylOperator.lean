/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Weyl's operator `Φ_λ` (§§6–7): definition, Lemma 1 and Lemma 2

Reference: H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
Annals of Mathematics 43 (1942), 381–407, pp. 398–403.

For a continuous `g` with `0 ≤ g ≤ 1` on `[0, ∞)` (Weyl's set `𝔊`, here `InG g`) put
`f' = J g`, `f = J (J g)`, `p = exp (2 ∫ f)`.  The solution `ω = Φ_λ{g}` of

  `φ'' + 2 f φ' + 2 (1 - 2λ) f' φ = 0`,  `φ(0) = 1`,  `φ ≥ 0`,  `φ' + 2 f φ ≤ 0`     ((37), (40))

is `ω = ψ / p`, where `(ψ, χ)` is the distinguished solution of the cooperative system
`ψ' = p χ`, `χ' = (4 λ f' / p) ψ` constructed in `WeylAux.lean`.

* `PhiL lam g`: Weyl's `Φ_λ{g}`;
* `PhiL_inG`: `Φ_λ` maps `𝔊` into `𝔊` (Weyl's `0 < Φ_λ{g} ≤ 1`, in the form `0 ≤ … ≤ 1`);
* `lw_le`: **Lemma 1**, `-ω'(0) = l ≤ c₁ = 1 + 2λ/3`;
* `Yw_le`: **Lemma 2**, `0 ≤ -p ω' ≤ c₁ + c₂ z²` with `c₂ = max (1 - 2λ) 0`;
* `PhiL_lipschitz`: the resulting equicontinuity, `|ω(x) - ω(y)| ≤ (c₁ + c₂ R²) |x - y|` on
  `[0, R]`.
-/
import WeylAux

open Set Filter Topology MeasureTheory

noncomputable section

namespace Blasius

lemma J_const (c z : ℝ) : J (fun _ => c) z = c * z := by
  simp [J, mul_comm]

/-- Weyl's set `𝔊`: continuous functions with values in `[0, 1]` on `[0, ∞)`. -/
structure InG (g : ℝ → ℝ) : Prop where
  cont : Continuous g
  nonneg : ∀ t, 0 ≤ t → 0 ≤ g t
  le_one : ∀ t, 0 ≤ t → g t ≤ 1

/-- `f' = ∫₀ᶻ g`. -/
def F1 (g : ℝ → ℝ) : ℝ → ℝ := J g

/-- `f = ∫₀ᶻ (z - ζ) g(ζ) dζ`, Weyl's (36). -/
def F0 (g : ℝ → ℝ) : ℝ → ℝ := J (F1 g)

/-- Weyl's `p(z) = exp (2 ∫₀ᶻ f)`. -/
def pp (g : ℝ → ℝ) (z : ℝ) : ℝ := Real.exp (2 * J (F0 g) z)

/-- Coefficient `a = p` (argument clamped at `0`). -/
def aL (g : ℝ → ℝ) (z : ℝ) : ℝ := pp g (max z 0)

/-- Coefficient `b = 4 λ f' / p` (argument clamped at `0`). -/
def bL (lam : ℝ) (g : ℝ → ℝ) (z : ℝ) : ℝ := 4 * lam * F1 g (max z 0) / pp g (max z 0)

/-- `ω = ψ / p` on `[0, ∞)` (unclamped). -/
def omg (lam : ℝ) (g : ℝ → ℝ) (z : ℝ) : ℝ := omψ (aL g) (bL lam g) z / pp g z

/-- **Weyl's operator** `Φ_λ{g}` (argument clamped at `0`). -/
def PhiL (lam : ℝ) (g : ℝ → ℝ) (z : ℝ) : ℝ := omg lam g (max z 0)

/-- Weyl's `-p ω'`, cf. (47), (49). -/
def Yw (lam : ℝ) (g : ℝ → ℝ) (z : ℝ) : ℝ :=
  -(pp g z * omχ (aL g) (bL lam g) z) + 2 * F0 g z * omψ (aL g) (bL lam g) z

/-- Weyl's constant `c₁` of Lemma 1 (the simple value `1 + 2λ/3`). -/
def c1 (lam : ℝ) : ℝ := 1 + 2 * lam / 3

/-- Weyl's constant `c₂` of Lemma 2. -/
def c2 (lam : ℝ) : ℝ := max (1 - 2 * lam) 0

namespace InG

variable {g : ℝ → ℝ} (hg : InG g)
include hg

lemma F1_continuous : Continuous (F1 g) := J_continuous hg.cont

lemma F0_continuous : Continuous (F0 g) := J_continuous hg.F1_continuous

lemma F1_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ F1 g z := J_nonneg hg.nonneg hz

/-- `f' ≤ z` (Weyl, p. 401). -/
lemma F1_le {z : ℝ} (hz : 0 ≤ z) : F1 g z ≤ z := by
  have := J_mono hg.cont continuous_const hg.le_one hz
  rwa [J_const, one_mul] at this

lemma F0_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ F0 g z := J_nonneg (fun _ ht => hg.F1_nonneg ht) hz

lemma hasDerivAt_F1 (z : ℝ) : HasDerivAt (F1 g) (g z) z := J_hasDerivAt hg.cont z

lemma hasDerivAt_F0 (z : ℝ) : HasDerivAt (F0 g) (F1 g z) z := J_hasDerivAt hg.F1_continuous z

omit hg in
lemma pp_pos (z : ℝ) : 0 < pp g z := Real.exp_pos _

lemma one_le_pp {z : ℝ} (hz : 0 ≤ z) : 1 ≤ pp g z := by
  rw [pp, Real.one_le_exp_iff]
  have := J_nonneg (g := F0 g) (fun _ ht => hg.F0_nonneg ht) hz
  linarith

lemma hasDerivAt_pp (z : ℝ) : HasDerivAt (pp g) (2 * F0 g z * pp g z) z := by
  have := ((J_hasDerivAt hg.F0_continuous z).const_mul 2).exp
  convert this using 1
  unfold pp
  ring

lemma pp_continuous : Continuous (pp g) :=
  continuous_iff_continuousAt.2 fun z => (hg.hasDerivAt_pp z).continuousAt

lemma coop {lam : ℝ} (hlam : 0 ≤ lam) : Coop (aL g) (bL lam g) where
  ca := hg.pp_continuous.comp (continuous_id.max continuous_const)
  cb := by
    have h1 := hg.F1_continuous
    have h2 := hg.pp_continuous
    have h3 : ∀ z : ℝ, pp g (max z 0) ≠ 0 := fun z => (pp_pos _).ne'
    have hmax : Continuous fun z : ℝ => max z 0 := continuous_id.max continuous_const
    exact (continuous_const.mul (h1.comp hmax)).div (h2.comp hmax) h3
  a1 := fun z => hg.one_le_pp (le_max_right z 0)
  b0 := fun z => by
    have := hg.F1_nonneg (le_max_right z 0)
    have := pp_pos (g := g) (max z 0)
    unfold bL
    positivity

omit hg in
lemma aL_eq {z : ℝ} (hz : 0 ≤ z) : aL g z = pp g z := by rw [aL, max_eq_left hz]

omit hg in
lemma bL_eq (lam : ℝ) {z : ℝ} (hz : 0 ≤ z) : bL lam g z = 4 * lam * F1 g z / pp g z := by
  rw [bL, max_eq_left hz]

section WithLam

variable {lam : ℝ} (hlam : 0 ≤ lam)
include hlam

/-- `ω' = χ - 2 f ω`, i.e. `ω₁ = p (ω' + 2 f ω)`. -/
lemma hasDerivAt_omg {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (omg lam g) (-(Yw lam g z / pp g z)) z := by
  have h1 := ((hg.coop hlam).om z).dψ z hz le_rfl
  rw [aL_eq hz] at h1
  have h2 := h1.div (hg.hasDerivAt_pp z) (pp_pos z).ne'
  convert h2 using 1
  have := (pp_pos (g := g) z).ne'
  unfold Yw
  field_simp
  ring

/-- `(-p ω')' = 2 (1 - 2λ) f' p ω` (Weyl, p. 403). -/
lemma hasDerivAt_Yw {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (Yw lam g)
      (2 * (1 - 2 * lam) * F1 g z * omψ (aL g) (bL lam g) z) z := by
  have hψ := ((hg.coop hlam).om z).dψ z hz le_rfl
  have hχ := ((hg.coop hlam).om z).dχ z hz le_rfl
  rw [aL_eq hz] at hψ
  rw [bL_eq lam hz] at hχ
  have := (((hg.hasDerivAt_pp z).mul hχ).neg).add
    ((((hg.hasDerivAt_F0 z).const_mul 2)).mul hψ)
  convert this using 1
  have := (pp_pos (g := g) z).ne'
  field_simp
  ring

lemma omψ_mem {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ omψ (aL g) (bL lam g) z ∧ omψ (aL g) (bL lam g) z ≤ 1 :=
  ⟨((hg.coop hlam).om_sign hz).1, (hg.coop hlam).omψ_le_one hz⟩

lemma omχ_nonpos {z : ℝ} (hz : 0 ≤ z) : omχ (aL g) (bL lam g) z ≤ 0 :=
  ((hg.coop hlam).om_sign hz).2

/-- `0 ≤ ω ≤ 1`. -/
lemma omg_mem {z : ℝ} (hz : 0 ≤ z) : 0 ≤ omg lam g z ∧ omg lam g z ≤ 1 := by
  obtain ⟨h0, h1⟩ := hg.omψ_mem hlam hz
  have hp := hg.one_le_pp hz
  constructor
  · exact div_nonneg h0 (pp_pos z).le
  · rw [omg, div_le_one (pp_pos z)]
    linarith

lemma Yw_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Yw lam g z := by
  have h1 := hg.omχ_nonpos hlam hz
  have h2 := (hg.omψ_mem hlam hz).1
  have h3 := hg.F0_nonneg hz
  have h4 := pp_pos (g := g) z
  have : 0 ≤ 2 * F0 g z * omψ (aL g) (bL lam g) z := by positivity
  have : pp g z * omχ (aL g) (bL lam g) z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h4.le h1
  unfold Yw
  linarith

omit hg hlam in
lemma Yw_zero : Yw lam g 0 = lw (aL g) (bL lam g) := by
  simp [Yw, pp, F0]

/-- `0 ≤ f' ω p ≤ z`: the product bound used in Lemmas 1 and 2. -/
lemma F1_mul_omψ {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ F1 g z * omψ (aL g) (bL lam g) z ∧ F1 g z * omψ (aL g) (bL lam g) z ≤ z := by
  obtain ⟨h0, h1⟩ := hg.omψ_mem hlam hz
  have h2 := hg.F1_nonneg hz
  have h3 := hg.F1_le hz
  exact ⟨mul_nonneg h2 h0, by nlinarith⟩

/-- `ω₁ / p ≤ -l + 2 λ z²` (Weyl, proof of Lemma 1). -/
lemma omχ_le {z : ℝ} (hz : 0 ≤ z) :
    omχ (aL g) (bL lam g) z ≤ -lw (aL g) (bL lam g) + 2 * lam * z ^ 2 := by
  have hanti := antitoneOn_Icc_of_hasDerivAt
    (F := fun x => omχ (aL g) (bL lam g) x - 2 * lam * x ^ 2)
    (F' := fun x => bL lam g x * omψ (aL g) (bL lam g) x - 2 * lam * (2 * x)) (s := 0) (t := z)
    (fun x h0 h1 => by
      have h2 : HasDerivAt (fun x : ℝ => 2 * lam * x ^ 2) (2 * lam * (2 * x)) x := by
        have := ((hasDerivAt_id x).pow 2).const_mul (2 * lam)
        convert this using 1
        simp
      exact (((hg.coop hlam).om z).dχ x h0 h1).sub h2)
    (fun x h0 _ => by
      beta_reduce
      rw [bL_eq lam h0]
      obtain ⟨h3, h4⟩ := hg.F1_mul_omψ hlam h0
      have hp := hg.one_le_pp h0
      have hpp := pp_pos (g := g) x
      have h5 : 4 * lam * F1 g x / pp g x * omψ (aL g) (bL lam g) x
          = 4 * lam * (F1 g x * omψ (aL g) (bL lam g) x) / pp g x := by ring
      have h6 : 4 * lam * (F1 g x * omψ (aL g) (bL lam g) x) / pp g x
          ≤ 4 * lam * (F1 g x * omψ (aL g) (bL lam g) x) :=
        div_le_self (by positivity) hp
      have h7 : 4 * lam * (F1 g x * omψ (aL g) (bL lam g) x) ≤ 4 * lam * x :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      rw [h5]
      linarith)
  have := hanti (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
  simp only [Coop.omχ_zero] at this
  nlinarith

/-- **Weyl's Lemma 1**: `-ω'(0) = l ≤ c₁`. -/
theorem lw_le : lw (aL g) (bL lam g) ≤ c1 lam := by
  have hanti := antitoneOn_Icc_of_hasDerivAt
    (F := fun x => omψ (aL g) (bL lam g) x + lw (aL g) (bL lam g) * x - 2 * lam / 3 * x ^ 3)
    (F' := fun x => aL g x * omχ (aL g) (bL lam g) x + lw (aL g) (bL lam g)
      - 2 * lam / 3 * (3 * x ^ 2)) (s := 0) (t := 1)
    (fun x h0 h1 => by
      have h2 : HasDerivAt (fun x : ℝ => 2 * lam / 3 * x ^ 3) (2 * lam / 3 * (3 * x ^ 2)) x := by
        have := ((hasDerivAt_id x).pow 3).const_mul (2 * lam / 3)
        convert this using 1
        simp
      have h3 : HasDerivAt (fun x : ℝ => lw (aL g) (bL lam g) * x) (lw (aL g) (bL lam g)) x := by
        simpa using (hasDerivAt_id x).const_mul (lw (aL g) (bL lam g))
      exact ((((hg.coop hlam).om 1).dψ x h0 h1).add h3).sub h2)
    (fun x h0 _ => by
      beta_reduce
      have h4 := hg.omχ_le hlam h0
      have h5 := hg.omχ_nonpos hlam h0
      have h6 : aL g x * omχ (aL g) (bL lam g) x ≤ omχ (aL g) (bL lam g) x := by
        have := (hg.coop hlam).a1 x
        nlinarith
      nlinarith)
  have := hanti (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [Coop.omψ_zero] at this
  have h1 := (hg.omψ_mem hlam zero_le_one).1
  unfold c1
  nlinarith

/-- **Weyl's Lemma 2**, (47): `-p ω' ≤ c₁ + c₂ z²`. -/
theorem Yw_le {z : ℝ} (hz : 0 ≤ z) : Yw lam g z ≤ c1 lam + c2 lam * z ^ 2 := by
  have hc2 : 0 ≤ c2 lam := le_max_right _ _
  have hc2' : 1 - 2 * lam ≤ c2 lam := le_max_left _ _
  have hanti := antitoneOn_Icc_of_hasDerivAt
    (F := fun x => Yw lam g x - c2 lam * x ^ 2)
    (F' := fun x => 2 * (1 - 2 * lam) * F1 g x * omψ (aL g) (bL lam g) x - c2 lam * (2 * x))
    (s := 0) (t := z)
    (fun x h0 _ => by
      have h2 : HasDerivAt (fun x : ℝ => c2 lam * x ^ 2) (c2 lam * (2 * x)) x := by
        have := ((hasDerivAt_id x).pow 2).const_mul (c2 lam)
        convert this using 1
        simp
      exact (hg.hasDerivAt_Yw hlam h0).sub h2)
    (fun x h0 _ => by
      beta_reduce
      obtain ⟨h3, h4⟩ := hg.F1_mul_omψ hlam h0
      have h5 : (1 - 2 * lam) * (F1 g x * omψ (aL g) (bL lam g) x)
          ≤ c2 lam * (F1 g x * omψ (aL g) (bL lam g) x) := mul_le_mul_of_nonneg_right hc2' h3
      have h6 : c2 lam * (F1 g x * omψ (aL g) (bL lam g) x) ≤ c2 lam * x :=
        mul_le_mul_of_nonneg_left h4 hc2
      nlinarith)
  have := hanti (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
  simp only [Yw_zero] at this
  have h1 := hg.lw_le hlam
  nlinarith

/-- (48): `0 ≤ -ω' ≤ c₁ + c₂ z²`. -/
lemma omg_deriv_mem {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ Yw lam g z / pp g z ∧ Yw lam g z / pp g z ≤ c1 lam + c2 lam * z ^ 2 := by
  have h1 := hg.Yw_nonneg hlam hz
  have h2 := hg.Yw_le hlam hz
  have hp := hg.one_le_pp hz
  exact ⟨div_nonneg h1 (pp_pos z).le, (div_le_self h1 hp).trans h2⟩

/-- `ω` is non-increasing on `[0, ∞)`. -/
lemma omg_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : omg lam g y ≤ omg lam g x := by
  have hanti := antitoneOn_Icc_of_hasDerivAt (F := omg lam g) (s := 0) (t := y)
    (fun u h0 _ => hg.hasDerivAt_omg hlam h0)
    (fun u h0 _ => by
      have := (hg.omg_deriv_mem hlam h0).1
      linarith)
  exact hanti ⟨hx, hxy⟩ (right_mem_Icc.2 (hx.trans hxy)) hxy

/-- Equicontinuity of the images `ω = Φ_λ{g}` (from Lemma 2). -/
lemma omg_lipschitz {R x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyR : y ≤ R) :
    omg lam g x - omg lam g y ≤ (c1 lam + c2 lam * R ^ 2) * (y - x) := by
  have hc2 : 0 ≤ c2 lam := le_max_right _ _
  have hmono := monotoneOn_Icc_of_hasDerivAt
    (F := fun u => omg lam g u + (c1 lam + c2 lam * R ^ 2) * u)
    (F' := fun u => -(Yw lam g u / pp g u) + (c1 lam + c2 lam * R ^ 2)) (s := 0) (t := R)
    (fun u h0 _ => by
      have h3 : HasDerivAt (fun u : ℝ => (c1 lam + c2 lam * R ^ 2) * u)
          (c1 lam + c2 lam * R ^ 2) u := by
        simpa using (hasDerivAt_id u).const_mul (c1 lam + c2 lam * R ^ 2)
      exact (hg.hasDerivAt_omg hlam h0).add h3)
    (fun u h0 h1 => by
      beta_reduce
      have := (hg.omg_deriv_mem hlam h0).2
      have : c2 lam * u ^ 2 ≤ c2 lam * R ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) hc2
      linarith)
  have := hmono ⟨hx, hxy.trans hyR⟩ ⟨hx.trans hxy, hyR⟩ hxy
  simp only at this
  linarith

/-- `Φ_λ` maps `𝔊` into `𝔊`. -/
theorem PhiL_inG : InG (PhiL lam g) where
  cont := by
    have hc : ContinuousOn (omg lam g) (Ici 0) := fun z hz =>
      (hg.hasDerivAt_omg hlam hz).continuousAt.continuousWithinAt
    exact hc.comp_continuous (continuous_id.max continuous_const) fun z => le_max_right z 0
  nonneg := fun t _ => (hg.omg_mem hlam (le_max_right t 0)).1
  le_one := fun t _ => (hg.omg_mem hlam (le_max_right t 0)).2

omit hg hlam in
lemma PhiL_eq {z : ℝ} (hz : 0 ≤ z) : PhiL lam g z = omg lam g z := by
  rw [PhiL, max_eq_left hz]

omit hg hlam in
@[simp] lemma PhiL_zero : PhiL lam g 0 = 1 := by
  simp [PhiL, omg, pp, F0]

/-- **Equicontinuity** of `Φ_λ{g}`, `g ∈ 𝔊`: Lipschitz on `[0, R]` with a constant independent
of `g` (Weyl's `𝔊_δ` with `δ(ε, z) = ε / (c₁ + c₂ z²)`). -/
theorem PhiL_lipschitz {R x y : ℝ} (hx : 0 ≤ x) (hxR : x ≤ R) (hy : 0 ≤ y) (hyR : y ≤ R) :
    |PhiL lam g x - PhiL lam g y| ≤ (c1 lam + c2 lam * R ^ 2) * |x - y| := by
  rw [PhiL_eq hx, PhiL_eq hy]
  rcases le_total x y with hxy | hxy
  · have h1 := hg.omg_antitone hlam hx hxy
    have h2 := hg.omg_lipschitz hlam hx hxy hyR
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h1 := hg.omg_antitone hlam hy hxy
    have h2 := hg.omg_lipschitz hlam hy hxy hxR
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

end WithLam

end InG

end Blasius

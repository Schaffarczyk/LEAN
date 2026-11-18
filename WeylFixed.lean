/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# From a fixed point of `Φ_λ` to a solution of problem `(A_λ)`

Reference: H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
Annals of Mathematics 43 (1942), 381–407, pp. 405–406.

Let `g ∈ 𝔊` be a fixed point of Weyl's operator, `g = Φ_λ{g}` on `[0, ∞)`, `λ > 0`, and
`f' = J g`, `f = J (J g)`.  Then (in the notation of `WeylOperator.lean`, `g = ψ / p`):

* `first_integral`: `χ = g' + 2 f g = -l + 2 λ f'²` (the integrated form of Weyl's (53));
* `F1_tendsto`: `f'` increases to a finite limit `β > 0` (immediate from `χ ≤ 0`);
* `lw_eq`: `l = 2 λ β²`, because `χ → 0`; otherwise `p g` would become negative;
* `hasDerivWithinAt_fixed`: `f''' + 2 f f'' + 2 λ (β² - f'²) = 0`;
* `weyl_Alam_of_fixed`: for every `k > 0`, `w(z) = κ f(κ z)` with `κ² β = k` solves

    `w''' + 2 w w'' + 2 λ (k² - w'²) = 0`,  `w(0) = w'(0) = 0`,  `w'(z) → k`   (problem `(A_λ)`),

  with `w'' ≥ 0` non-increasing.

Weyl obtains `β < ∞` and `l = 2 λ β²` from the Gaussian decay of his Lemmas 3 and 4; the
argument here uses only `p ≥ 1`, `ψ ≥ 0`, `χ ≤ 0`.  The decay estimates themselves are not
formalised.
-/
import WeylContinuity

open Set Filter Topology MeasureTheory

noncomputable section

namespace Blasius

namespace InG

variable {g : ℝ → ℝ} {lam : ℝ} (hg : InG g) (hlam : 0 < lam)
  (hfix : ∀ z, 0 ≤ z → PhiL lam g z = g z)
include hg hlam hfix

omit hg hlam in
lemma fixed_eq {z : ℝ} (hz : 0 ≤ z) : g z = omψ (aL g) (bL lam g) z / pp g z := by
  rw [← hfix z hz, PhiL_eq hz]
  rfl

omit hg hlam in
lemma fixed_zero : g 0 = 1 := by
  rw [← hfix 0 le_rfl]
  exact PhiL_zero

/-- The first integral `χ - 2 λ f'² = -l`, cf. Weyl's (53). -/
lemma first_integral {z : ℝ} (hz : 0 ≤ z) :
    omχ (aL g) (bL lam g) z = -lw (aL g) (bL lam g) + 2 * lam * F1 g z ^ 2 := by
  have := eq_of_hasDerivAt_zero
    (F := fun x => omχ (aL g) (bL lam g) x - 2 * lam * F1 g x ^ 2) hz
    (fun x h0 h1 => by
      have h2 := ((hg.coop hlam.le).om z).dχ x h0 h1
      rw [bL_eq lam h0] at h2
      have h3 := ((hg.hasDerivAt_F1 x).pow 2).const_mul (2 * lam)
      have h4 := h2.sub h3
      deriv_conv h4
      rw [fixed_eq hfix h0]
      have := (pp_pos (g := g) x).ne'
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      field_simp
      ring)
  simp only [Coop.omχ_zero, F1, J_apply_zero] at this
  simp only [F1]
  linarith

/-- Quantitative form of Weyl's Lemma 3: `f'(z₀) ≥ z₀ / 2` for `z₀ = 1 / (c₁ + c₂)`. -/
lemma F1_pos : 0 < F1 g (1 / (c1 lam + c2 lam)) := by
  have hc2 : 0 ≤ c2 lam := le_max_right _ _
  have hc1 : 1 ≤ c1 lam := by
    unfold c1
    have : 0 ≤ 2 * lam / 3 := by positivity
    linarith
  set K := c1 lam + c2 lam with hK
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := by linarith
  have hz0 : 0 < 1 / K := by positivity
  have hz1 : 1 / K ≤ 1 := by
    rw [div_le_one hK0]
    exact hK1
  -- `g(z) ≥ 1 - K z` on `[0, 1]`
  have hlow : ∀ x, 0 ≤ x → x ≤ 1 → 1 - K * x ≤ g x := by
    intro x h0 h1
    have h2 := hg.omg_lipschitz hlam.le (R := 1) le_rfl h0 h1
    have e0 : omg lam g 0 = 1 := by
      rw [← PhiL_eq le_rfl]
      exact PhiL_zero
    rw [e0, ← PhiL_eq h0, hfix x h0] at h2
    simp only [one_pow, mul_one, sub_zero] at h2
    linarith
  have hm := monotoneOn_Icc_of_hasDerivAt
    (F := fun x => F1 g x - (x - K * x ^ 2 / 2)) (F' := fun x => g x - (1 - K * x))
    (s := 0) (t := 1 / K)
    (fun x _ _ => by
      have h3 : HasDerivAt (fun x : ℝ => x - K * x ^ 2 / 2) (1 - K * x) x := by
        have := (hasDerivAt_id x).sub ((((hasDerivAt_id x).pow 2).const_mul K).div_const 2)
        deriv_conv this
        simp
        ring
      exact (hg.hasDerivAt_F1 x).sub h3)
    (fun x h0 h1 => by
      linarith [hlow x h0 (h1.trans hz1)])
  have := hm (left_mem_Icc.2 hz0.le) (right_mem_Icc.2 hz0.le) hz0.le
  simp only [F1, J_apply_zero] at this
  have e : 1 / K - K * (1 / K) ^ 2 / 2 = 1 / K / 2 := by
    field_simp
    ring
  rw [e] at this
  have : 0 < 1 / K / 2 := by positivity
  simp only [F1]
  linarith

omit hlam hfix in
lemma F1_monotoneOn {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : F1 g x ≤ F1 g y := by
  have hm := monotoneOn_Icc_of_hasDerivAt (F := F1 g) (s := 0) (t := y)
    (fun u _ _ => hg.hasDerivAt_F1 u) (fun u h0 _ => hg.nonneg u h0)
  exact hm ⟨hx, hxy⟩ (right_mem_Icc.2 (hx.trans hxy)) hxy

/-- `2 λ f'² ≤ l`: the boundedness of `f'`. -/
lemma F1_sq_le {z : ℝ} (hz : 0 ≤ z) : 2 * lam * F1 g z ^ 2 ≤ lw (aL g) (bL lam g) := by
  have h1 := hg.first_integral hlam hfix hz
  have h2 := hg.omχ_nonpos hlam.le hz
  linarith

/-- Weyl's constant `β = lim f'`. -/
def betaL (g : ℝ → ℝ) : ℝ := ⨆ z : ℝ, F1 g (max z 0)

omit hlam hfix in
lemma F1c_mono : Monotone fun z : ℝ => F1 g (max z 0) := fun x _ hxy =>
  hg.F1_monotoneOn (le_max_right x 0) (max_le_max hxy le_rfl)

lemma F1c_bdd : BddAbove (range fun z : ℝ => F1 g (max z 0)) := by
  refine ⟨lw (aL g) (bL lam g) / (2 * lam) + 1, ?_⟩
  rintro _ ⟨z, rfl⟩
  have h1 := hg.F1_sq_le hlam hfix (le_max_right z 0)
  have h2 : F1 g (max z 0) ^ 2 ≤ lw (aL g) (bL lam g) / (2 * lam) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  nlinarith [sq_nonneg (F1 g (max z 0) - 1)]

lemma F1_le_beta {z : ℝ} (hz : 0 ≤ z) : F1 g z ≤ betaL g := by
  have := le_ciSup (hg.F1c_bdd hlam hfix) z
  rwa [max_eq_left hz] at this

/-- `f'(z) → β`. -/
lemma F1_tendsto : Tendsto (F1 g) atTop (𝓝 (betaL g)) := by
  have h := tendsto_atTop_ciSup hg.F1c_mono (hg.F1c_bdd hlam hfix)
  refine h.congr' ((eventually_ge_atTop 0).mono fun z hz => ?_)
  simp only [max_eq_left hz]

lemma betaL_pos : 0 < betaL g :=
  lt_of_lt_of_le (hg.F1_pos hlam hfix)
    (hg.F1_le_beta hlam hfix (by
      have hc2 : 0 ≤ c2 lam := le_max_right _ _
      have : 0 < c1 lam := by
        unfold c1
        positivity
      positivity))

/-- `l = 2 λ β²`: the constant in Weyl's (53) is `-2 λ β²`. -/
theorem lw_eq : lw (aL g) (bL lam g) = 2 * lam * betaL g ^ 2 := by
  have hβ := hg.betaL_pos hlam hfix
  -- `χ → s := -l + 2 λ β²`
  have hχ : Tendsto (omχ (aL g) (bL lam g)) atTop
      (𝓝 (-lw (aL g) (bL lam g) + 2 * lam * betaL g ^ 2)) := by
    have h1 := (((hg.F1_tendsto hlam hfix).pow 2).const_mul (2 * lam)).const_add
      (-lw (aL g) (bL lam g))
    refine h1.congr' ((eventually_ge_atTop 0).mono fun z hz => ?_)
    exact (hg.first_integral hlam hfix hz).symm
  have hs0 : -lw (aL g) (bL lam g) + 2 * lam * betaL g ^ 2 ≤ 0 :=
    le_of_tendsto hχ ((eventually_ge_atTop 0).mono fun z hz => hg.omχ_nonpos hlam.le hz)
  -- `χ ≤ s` on `[0, ∞)`
  have hle : ∀ z, 0 ≤ z →
      omχ (aL g) (bL lam g) z ≤ -lw (aL g) (bL lam g) + 2 * lam * betaL g ^ 2 := by
    intro z hz
    rw [hg.first_integral hlam hfix hz]
    have h1 := hg.F1_nonneg hz
    have h2 := hg.F1_le_beta hlam hfix hz
    have : F1 g z ^ 2 ≤ betaL g ^ 2 := pow_le_pow_left₀ h1 h2 2
    nlinarith
  by_contra hne
  have hs : -lw (aL g) (bL lam g) + 2 * lam * betaL g ^ 2 < 0 :=
    lt_of_le_of_ne hs0 fun h => hne (by linarith)
  set s := -lw (aL g) (bL lam g) + 2 * lam * betaL g ^ 2 with hsdef
  -- then `ψ' = p χ ≤ s < 0`, so `ψ` becomes negative
  have hz : 0 ≤ -2 / s := by
    have : 2 / s < 0 := div_neg_of_pos_of_neg two_pos hs
    rw [neg_div]
    linarith
  have hanti := antitoneOn_Icc_of_hasDerivAt
    (F := fun x => omψ (aL g) (bL lam g) x - s * x)
    (F' := fun x => aL g x * omχ (aL g) (bL lam g) x - s) (s := 0) (t := -2 / s)
    (fun x h0 h1 => by
      have h3 : HasDerivAt (fun x : ℝ => s * x) s x := by
        simpa using (hasDerivAt_id x).const_mul s
      exact (((hg.coop hlam.le).om _).dψ x h0 h1).sub h3)
    (fun x h0 _ => by
      have h1 := hle x h0
      have h2 := (hg.coop hlam.le).a1 x
      have h3 := hg.omχ_nonpos hlam.le h0
      nlinarith)
  have h1 := hanti (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
  simp only [Coop.omψ_zero, mul_zero, sub_zero] at h1
  have h2 := (hg.omψ_mem hlam.le hz).1
  have e : s * (-2 / s) = -2 := by
    have := hs.ne
    field_simp
  rw [e] at h1
  linarith

/-- **The differential equation** `f''' + 2 f f'' + 2 λ (β² - f'²) = 0` for the fixed point
`g = f''` (one-sided derivative at `0`). -/
theorem hasDerivWithinAt_fixed {z : ℝ} (hz : 0 ≤ z) :
    HasDerivWithinAt g (-(2 * F0 g z * g z) - 2 * lam * (betaL g ^ 2 - F1 g z ^ 2)) (Ici 0) z := by
  have h1 := (hg.hasDerivAt_omg hlam.le hz).hasDerivWithinAt (s := Ici 0)
  have e : -(Yw lam g z / pp g z) = -(2 * F0 g z * g z) - 2 * lam * (betaL g ^ 2 - F1 g z ^ 2) := by
    have h2 := hg.first_integral hlam hfix hz
    have h3 := hg.lw_eq hlam hfix
    have hp := (pp_pos (g := g) z).ne'
    rw [fixed_eq hfix hz]
    unfold Yw
    rw [h2, h3]
    field_simp
    ring
  rw [e] at h1
  refine h1.congr (fun x hx => ?_) ?_
  · rw [← hfix x hx, PhiL_eq hx]
  · rw [← hfix z hz, PhiL_eq hz]

lemma fixed_antitoneOn : AntitoneOn g (Ici 0) := by
  intro x hx y hy hxy
  rw [← hfix x hx, ← hfix y (mem_Ici.1 hy), PhiL_eq hx, PhiL_eq (mem_Ici.1 hy)]
  exact hg.omg_antitone hlam.le hx hxy

/-- **Problem `(A_λ)` from a fixed point** of `Φ_λ`: for every `k > 0` there is `w` with
`w''' + 2 w w'' + 2 λ (k² - w'²) = 0` on `[0, ∞)`, `w(0) = w'(0) = 0`, `w'(z) → k`;
moreover `w'' ≥ 0` is non-increasing.  Here `w₁ = w'`, `w₂ = w''`. -/
theorem weyl_Alam_of_fixed (k : ℝ) (hk : 0 < k) :
    ∃ w w₁ w₂ : ℝ → ℝ,
      (∀ z, HasDerivAt w (w₁ z) z) ∧
      (∀ z, HasDerivAt w₁ (w₂ z) z) ∧
      (∀ z, 0 ≤ z → HasDerivWithinAt w₂
        (-(2 * w z * w₂ z) - 2 * lam * (k ^ 2 - w₁ z ^ 2)) (Ici 0) z) ∧
      w 0 = 0 ∧ w₁ 0 = 0 ∧ Tendsto w₁ atTop (𝓝 k) ∧
      (∀ z, 0 ≤ z → 0 ≤ w₂ z) ∧ AntitoneOn w₂ (Ici 0) := by
  have hβ := hg.betaL_pos hlam hfix
  set c := Real.sqrt (k / betaL g) with hcdef
  have hc : 0 < c := Real.sqrt_pos.2 (div_pos hk hβ)
  have hc2 : c ^ 2 * betaL g = k := by
    rw [hcdef, Real.sq_sqrt (div_pos hk hβ).le, div_mul_cancel₀ _ hβ.ne']
  have hlin : ∀ z : ℝ, HasDerivAt (fun z => c * z) c z := fun z => by
    simpa using (hasDerivAt_id z).const_mul c
  have hmaps : MapsTo (fun z => c * z) (Ici (0 : ℝ)) (Ici 0) := fun x hx => mul_nonneg hc.le hx
  refine ⟨fun z => c * F0 g (c * z), fun z => c ^ 2 * F1 g (c * z), fun z => c ^ 3 * g (c * z),
    fun z => ?_, fun z => ?_, fun z hz => ?_, by simp [F0], by simp [F1], ?_, fun z hz => ?_,
    fun x hx y hy hxy => ?_⟩
  · have := ((hg.hasDerivAt_F0 (c * z)).comp z (hlin z)).const_mul c
    deriv_conv this
    ring
  · have := ((hg.hasDerivAt_F1 (c * z)).comp z (hlin z)).const_mul (c ^ 2)
    deriv_conv this
    ring
  · have := ((hg.hasDerivWithinAt_fixed hlam hfix (mul_nonneg hc.le hz)).comp z
      (hlin z).hasDerivWithinAt hmaps).const_mul (c ^ 3)
    deriv_conv this
    rw [← hc2]
    ring
  · have h1 : Tendsto (fun z => c * z) atTop atTop := tendsto_id.const_mul_atTop hc
    have h2 := ((hg.F1_tendsto hlam hfix).comp h1).const_mul (c ^ 2)
    rw [hc2] at h2
    exact h2
  · exact mul_nonneg (by positivity) (hg.nonneg _ (mul_nonneg hc.le hz))
  · exact mul_le_mul_of_nonneg_left
      (hg.fixed_antitoneOn hlam hfix (mem_Ici.2 (mul_nonneg hc.le hx))
        (mem_Ici.2 (mul_nonneg hc.le hy)) (mul_le_mul_of_nonneg_left hxy hc.le)) (by positivity)

end InG

end Blasius

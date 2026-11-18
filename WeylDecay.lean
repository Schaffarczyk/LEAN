/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Weyl's Lemmas 3 and 4 and the theorem of p. 406 in full

Reference: H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
Annals of Mathematics 43 (1942), 381–407, pp. 403–406.

For a fixed point `g = Φ_λ{g}`, `λ > 0`:

* `InG.F1_one_ge`: **Lemma 3**, `∫₀¹ g ≥ c > 0` with `c = 1 / (2 (c₁ + c₂))` (Weyl has the
  slightly better constant `c₃ / 2`, `1 / c₃ = max (1, c₁ + c₂ / 6)`);
* `InG.omg_le_gauss`, `InG.chi_decay`: **Lemma 4**, for `ω = Φ_λ{g}`, `g ∈ 𝔊`, `γ = ∫₀¹ g`:
  `ω(z) ≤ e^{-γ (z-1)²}` and `0 ≤ -(ω' + 2 f ω) ≤ (c₁ + c₂ z²) e^{-γ (z-1)²}` for `z ≥ 1`;
  `InG.fixed_le_gauss` is (52) for the fixed point;
* `InG.betaL_le`, `weyl_theorem_bounds`: Weyl's explicit appraisal of `β` and the resulting
  two-sided bound for `w''(0)`;
* `weyl_theorem`: **the theorem of p. 406** for all `λ ≥ 0`: the problem `(A_λ)` has a
  solution `w` whose derivative increases monotonically from `0` to `k`, and whose second
  derivative decreases monotonically from `w''(0) > 0` to zero at least as fast as
  `C e^{-γ z²}`.
-/
import WeylMain
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Set Filter Topology MeasureTheory

noncomputable section

namespace Blasius

namespace InG

variable {g : ℝ → ℝ} {lam : ℝ} (hg : InG g)
include hg

/-- `p(z) ≥ e^{γ (z-1)²}` for `z ≥ 1`, `γ = ∫₀¹ g` (proof of Lemma 4). -/
lemma pp_ge {z : ℝ} (hz : 1 ≤ z) : Real.exp (F1 g 1 * (z - 1) ^ 2) ≤ pp g z := by
  have hF1 : ∀ x, 1 ≤ x → F1 g 1 ≤ F1 g x := fun x hx => by
    have hm := monotoneOn_Icc_of_hasDerivAt (F := F1 g) (s := 0) (t := x)
      (fun u _ _ => hg.hasDerivAt_F1 u) (fun u h0 _ => hg.nonneg u h0)
    exact hm ⟨zero_le_one, hx⟩ (right_mem_Icc.2 (zero_le_one.trans hx)) hx
  have hF0 : ∀ x, 1 ≤ x → F1 g 1 * (x - 1) ≤ F0 g x := fun x hx => by
    have hm := monotoneOn_Icc_of_hasDerivAt (F := fun u => F0 g u - F1 g 1 * (u - 1))
      (F' := fun u => F1 g u - F1 g 1) (s := 1) (t := x)
      (fun u _ _ => by
        have h1 : HasDerivAt (fun u : ℝ => F1 g 1 * (u - 1)) (F1 g 1) u := by
          simpa using ((hasDerivAt_id u).sub_const 1).const_mul (F1 g 1)
        exact (hg.hasDerivAt_F0 u).sub h1)
      (fun u hu _ => sub_nonneg.2 (hF1 u hu))
    have := hm (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx
    simp only [sub_self, mul_zero, sub_zero] at this
    linarith [hg.F0_nonneg zero_le_one]
  have hJ : F1 g 1 * (z - 1) ^ 2 / 2 ≤ J (F0 g) z := by
    have hm := monotoneOn_Icc_of_hasDerivAt
      (F := fun u => J (F0 g) u - F1 g 1 * (u - 1) ^ 2 / 2)
      (F' := fun u => F0 g u - F1 g 1 * (u - 1)) (s := 1) (t := z)
      (fun u _ _ => by
        have h1 : HasDerivAt (fun u : ℝ => F1 g 1 * (u - 1) ^ 2 / 2) (F1 g 1 * (u - 1)) u := by
          have := ((((hasDerivAt_id u).sub_const 1).pow 2).const_mul (F1 g 1)).div_const 2
          deriv_conv this
          simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
          ring
        exact (J_hasDerivAt hg.F0_continuous u).sub h1)
      (fun u hu _ => sub_nonneg.2 (hF0 u hu))
    have := hm (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
    simp only [sub_self] at this
    have h0 : 0 ≤ J (F0 g) 1 := J_nonneg (fun _ ht => hg.F0_nonneg ht) zero_le_one
    norm_num at this
    linarith
  rw [pp, Real.exp_le_exp]
  linarith

/-- **Lemma 4**, first part: `ω(z) = Φ_λ{g}(z) ≤ e^{-γ (z-1)²}` for `z ≥ 1`, `γ = ∫₀¹ g`. -/
theorem omg_le_gauss (hlam0 : 0 ≤ lam) {z : ℝ} (hz : 1 ≤ z) :
    omg lam g z ≤ Real.exp (-(F1 g 1 * (z - 1) ^ 2)) := by
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  have h1 := (hg.omψ_mem hlam0 hz0).2
  have h2 := hg.pp_ge hz
  have h3 : Real.exp (-(F1 g 1 * (z - 1) ^ 2)) * Real.exp (F1 g 1 * (z - 1) ^ 2) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [omg, div_le_iff₀ (pp_pos z)]
  have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-(F1 g 1 * (z - 1) ^ 2))).le
  linarith

variable (hlam : 0 < lam) (hfix : ∀ z, 0 ≤ z → PhiL lam g z = g z)
include hlam hfix

/-- **Lemma 3**: `∫₀¹ g ≥ 1 / (2 (c₁ + c₂)) > 0`. -/
theorem F1_one_ge : 1 / (2 * (c1 lam + c2 lam)) ≤ F1 g 1 := by
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
  have e : 1 / K - K * (1 / K) ^ 2 / 2 = 1 / (2 * K) := by
    field_simp
    ring
  rw [e] at this
  have hmono := monotoneOn_Icc_of_hasDerivAt (F := F1 g) (s := 0) (t := 1)
    (fun u _ _ => hg.hasDerivAt_F1 u) (fun u h0 _ => hg.nonneg u h0)
  have h1 := hmono ⟨hz0.le, hz1⟩ (right_mem_Icc.2 zero_le_one) hz1
  simp only [F1] at h1 ⊢
  linarith

lemma F1_one_pos : 0 < F1 g 1 := by
  have hc2 : 0 ≤ c2 lam := le_max_right _ _
  have hc1 : 0 < c1 lam := by
    unfold c1
    positivity
  have : 0 < 1 / (2 * (c1 lam + c2 lam)) := by positivity
  exact lt_of_lt_of_le this (hg.F1_one_ge hlam hfix)

/-- (52): `g(z) ≤ e^{-γ (z-1)²}` for `z ≥ 1`, for a fixed point `g`. -/
theorem fixed_le_gauss {z : ℝ} (hz : 1 ≤ z) : g z ≤ Real.exp (-(F1 g 1 * (z - 1) ^ 2)) := by
  rw [← hfix z (zero_le_one.trans hz), PhiL_eq (zero_le_one.trans hz)]
  exact hg.omg_le_gauss hlam.le hz

omit hfix in
/-- **Lemma 4**, second part: `0 ≤ -(ω' + 2 f ω) ≤ (c₁ + c₂ z²) e^{-γ (z-1)²}` for `z ≥ 1`;
here `ω' + 2 f ω = χ`. -/
theorem chi_decay {z : ℝ} (hz : 1 ≤ z) :
    0 ≤ -omχ (aL g) (bL lam g) z ∧
      -omχ (aL g) (bL lam g) z
        ≤ (c1 lam + c2 lam * z ^ 2) * Real.exp (-(F1 g 1 * (z - 1) ^ 2)) := by
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  have h0 := hg.omχ_nonpos hlam.le hz0
  refine ⟨by linarith, ?_⟩
  have hY := hg.Yw_le hlam.le hz0
  have hψ := (hg.omψ_mem hlam.le hz0).1
  have hF := hg.F0_nonneg hz0
  have hp := pp_pos (g := g) z
  have h2 := hg.pp_ge hz
  have h3 : Real.exp (-(F1 g 1 * (z - 1) ^ 2)) * Real.exp (F1 g 1 * (z - 1) ^ 2) = 1 := by
    rw [← Real.exp_add]
    simp
  have hE := Real.exp_pos (-(F1 g 1 * (z - 1) ^ 2))
  -- `-p χ ≤ c₁ + c₂ z²`
  have h4 : pp g z * -omχ (aL g) (bL lam g) z ≤ c1 lam + c2 lam * z ^ 2 := by
    have : 0 ≤ 2 * F0 g z * omψ (aL g) (bL lam g) z := by positivity
    unfold Yw at hY
    linarith
  -- `-χ ≤ -χ p e^{-γ(z-1)²}`
  have h5 : -omχ (aL g) (bL lam g) z
      ≤ pp g z * -omχ (aL g) (bL lam g) z * Real.exp (-(F1 g 1 * (z - 1) ^ 2)) := by
    have h6 : 1 ≤ pp g z * Real.exp (-(F1 g 1 * (z - 1) ^ 2)) := by
      have := mul_le_mul_of_nonneg_left h2 hE.le
      linarith
    have := mul_le_mul_of_nonneg_left h6 (show 0 ≤ -omχ (aL g) (bL lam g) z by linarith)
    linarith
  exact h5.trans (mul_le_mul_of_nonneg_right h4 hE.le)

/-- Gaussian bound on all of `[0, ∞)`. -/
lemma fixed_le_gauss' {z : ℝ} (hz : 0 ≤ z) :
    g z ≤ Real.exp (F1 g 1) * Real.exp (-(F1 g 1 / 2 * z ^ 2)) := by
  have hγ := hg.F1_nonneg zero_le_one
  rw [← Real.exp_add]
  rcases le_total z 1 with h | h
  · refine (hg.le_one z hz).trans (Real.one_le_exp ?_)
    nlinarith [mul_nonneg hγ (sub_nonneg.2 h), mul_nonneg (mul_nonneg hγ hz) (sub_nonneg.2 h)]
  · refine (hg.fixed_le_gauss hlam hfix h).trans (Real.exp_le_exp.2 ?_)
    nlinarith [mul_nonneg hγ (sq_nonneg (z - 2))]

/-- Weyl's explicit appraisal of `β` (p. 405): `β ≤ 1 + ½ √(π/γ)`, `γ = ∫₀¹ g`. -/
theorem betaL_le : betaL g ≤ 1 + Real.sqrt (Real.pi / F1 g 1) / 2 := by
  have hγ := hg.F1_one_pos hlam hfix
  set G : ℝ → ℝ := fun s => Real.exp (-F1 g 1 * s ^ 2) with hG
  have hGc : Continuous G := by fun_prop
  have hGpos : ∀ s, 0 < G s := fun s => Real.exp_pos _
  have hint : IntegrableOn G (Ioi 0) := (integrable_exp_neg_mul_sq hγ).integrableOn
  have hval : ∫ s in Ioi (0 : ℝ), G s = Real.sqrt (Real.pi / F1 g 1) / 2 :=
    integral_gaussian_Ioi (F1 g 1)
  have hJt : Tendsto (J G) atTop (𝓝 (∫ s in Ioi (0 : ℝ), G s)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hJmono : Monotone (J G) :=
    monotone_of_deriv_nonneg (fun x => (J_hasDerivAt hGc x).differentiableAt) fun x => by
      rw [(J_hasDerivAt hGc x).deriv]
      exact (hGpos x).le
  have hJle : ∀ y, J G y ≤ ∫ s in Ioi (0 : ℝ), G s := fun y =>
    ge_of_tendsto hJt ((eventually_ge_atTop y).mono fun _ h => hJmono h)
  have key : ∀ z, 1 ≤ z → F1 g z ≤ 1 + Real.sqrt (Real.pi / F1 g 1) / 2 := by
    intro z hz
    have hm := monotoneOn_Icc_of_hasDerivAt (F := fun x => J G (x - 1) - F1 g x)
      (F' := fun x => G (x - 1) - g x) (s := 1) (t := z)
      (fun x _ _ => by
        have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 x := (hasDerivAt_id x).sub_const 1
        have h2 := (J_hasDerivAt hGc (x - 1)).comp x h1
        have h3 := h2.sub (hg.hasDerivAt_F1 x)
        deriv_conv h3
        ring)
      (fun x hx _ => by
        have := hg.fixed_le_gauss hlam hfix hx
        have e : G (x - 1) = Real.exp (-(F1 g 1 * (x - 1) ^ 2)) := by
          simp only [hG]
          congr 1
          ring
        rw [e]
        linarith)
    have := hm (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
    simp only [sub_self, J_apply_zero, zero_sub] at this
    have h1 := hg.F1_le zero_le_one
    have h2 := hJle (z - 1)
    rw [hval] at h2
    linarith
  exact le_of_tendsto (hg.F1_tendsto hlam hfix) ((eventually_ge_atTop 1).mono key)

/-- `β ≥ γ = ∫₀¹ g`. -/
lemma betaL_ge : F1 g 1 ≤ betaL g := hg.F1_le_beta hlam hfix zero_le_one

end InG

/-- The properties of the solution of `(A_λ)` in Weyl's theorem, p. 406
(`w₁ = w'`, `w₂ = w''`). -/
structure IsWeylSol (lam k : ℝ) (w w₁ w₂ : ℝ → ℝ) : Prop where
  d0 : ∀ z, HasDerivAt w (w₁ z) z
  d1 : ∀ z, HasDerivAt w₁ (w₂ z) z
  /-- the differential equation `w''' + 2 w w'' + 2 λ (k² - w'²) = 0` on `[0, ∞)` -/
  d2 : ∀ z, 0 ≤ z → HasDerivWithinAt w₂
    (-(2 * w z * w₂ z) - 2 * lam * (k ^ 2 - w₁ z ^ 2)) (Ici 0) z
  z0 : w 0 = 0
  z1 : w₁ 0 = 0
  lim : Tendsto w₁ atTop (𝓝 k)
  /-- `w'` increases monotonically from `0` to `k` -/
  w1_mono : MonotoneOn w₁ (Ici 0)
  w1_le : ∀ z, 0 ≤ z → w₁ z ≤ k
  /-- `w''` decreases monotonically from `w''(0) > 0` to zero -/
  w2_zero_pos : 0 < w₂ 0
  w2_nonneg : ∀ z, 0 ≤ z → 0 ≤ w₂ z
  w2_anti : AntitoneOn w₂ (Ici 0)
  /-- Gaussian decay of `w''` -/
  w2_decay : ∃ C γ : ℝ, 0 < γ ∧ ∀ z, 0 ≤ z → w₂ z ≤ C * Real.exp (-(γ * z ^ 2))

/-- Weyl's theorem from a fixed point of `Φ_λ`, `λ > 0`. -/
theorem InG.weyl_theorem_of_fixed {g : ℝ → ℝ} {lam : ℝ} (hg : InG g) (hlam : 0 < lam)
    (hfix : ∀ z, 0 ≤ z → PhiL lam g z = g z) (k : ℝ) (hk : 0 < k) :
    ∃ w w₁ w₂ : ℝ → ℝ, IsWeylSol lam k w w₁ w₂ ∧ w₂ 0 ^ 2 * InG.betaL g ^ 3 = k ^ 3 := by
  have hβ := hg.betaL_pos hlam hfix
  have hγ := hg.F1_one_pos hlam hfix
  set c := Real.sqrt (k / InG.betaL g) with hcdef
  have hc : 0 < c := Real.sqrt_pos.2 (div_pos hk hβ)
  have hc2 : c ^ 2 * InG.betaL g = k := by
    rw [hcdef, Real.sq_sqrt (div_pos hk hβ).le, div_mul_cancel₀ _ hβ.ne']
  have hlin : ∀ z : ℝ, HasDerivAt (fun z => c * z) c z := fun z => by
    simpa using (hasDerivAt_id z).const_mul c
  have hmaps : MapsTo (fun z => c * z) (Ici (0 : ℝ)) (Ici 0) := fun x hx => mul_nonneg hc.le hx
  refine ⟨fun z => c * F0 g (c * z), fun z => c ^ 2 * F1 g (c * z), fun z => c ^ 3 * g (c * z),
    ⟨fun z => ?_, fun z => ?_, fun z hz => ?_, by simp [F0], by simp [F1], ?_,
      fun x hx y hy hxy => ?_, fun z hz => ?_, ?_, fun z hz => ?_, fun x hx y hy hxy => ?_,
      ⟨c ^ 3 * Real.exp (F1 g 1), F1 g 1 / 2 * c ^ 2, by positivity, fun z hz => ?_⟩⟩, ?_⟩
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
  · exact mul_le_mul_of_nonneg_left
      (hg.F1_monotoneOn (mul_nonneg hc.le hx) (mul_le_mul_of_nonneg_left hxy hc.le))
      (by positivity)
  · have := hg.F1_le_beta hlam hfix (mul_nonneg hc.le hz)
    calc c ^ 2 * F1 g (c * z) ≤ c ^ 2 * InG.betaL g :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = k := hc2
  · show 0 < c ^ 3 * g (c * 0)
    rw [mul_zero, InG.fixed_zero hfix]
    positivity
  · exact mul_nonneg (by positivity) (hg.nonneg _ (mul_nonneg hc.le hz))
  · exact mul_le_mul_of_nonneg_left
      (hg.fixed_antitoneOn hlam hfix (mem_Ici.2 (mul_nonneg hc.le hx))
        (mem_Ici.2 (mul_nonneg hc.le hy)) (mul_le_mul_of_nonneg_left hxy hc.le)) (by positivity)
  · have := hg.fixed_le_gauss' hlam hfix (mul_nonneg hc.le hz)
    calc c ^ 3 * g (c * z)
        ≤ c ^ 3 * (Real.exp (F1 g 1) * Real.exp (-(F1 g 1 / 2 * (c * z) ^ 2))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = c ^ 3 * Real.exp (F1 g 1) * Real.exp (-(F1 g 1 / 2 * c ^ 2 * z ^ 2)) := by
          rw [mul_assoc]
          congr 3
          ring
  · show (c ^ 3 * g (c * 0)) ^ 2 * InG.betaL g ^ 3 = k ^ 3
    rw [mul_zero, InG.fixed_zero hfix, ← hc2]
    ring

/-- **Weyl's theorem (p. 406)**: for `λ ≥ 0` and `k > 0` the problem `(A_λ)`,

  `w''' + 2 w w'' + 2 λ (k² - w'²) = 0`,  `w(0) = w'(0) = 0`,  `w'(∞) = k`,

has a solution `w` whose derivative is monotone increasing from `0` to `k`, and whose second
derivative decreases monotonically from `w''(0) > 0` to zero, at least as strongly as a
function `C e^{-γ z²}`, `γ > 0`. -/
theorem weyl_theorem {lam : ℝ} (hlam : 0 ≤ lam) (k : ℝ) (hk : 0 < k) :
    ∃ w w₁ w₂ : ℝ → ℝ, IsWeylSol lam k w w₁ w₂ := by
  rcases hlam.eq_or_lt with rfl | hpos
  · obtain ⟨w, w₁, w₂, d0, d1, d2, z0, z1, hl⟩ := weyl_A0_exists k hk
    have hs : IsSol w w₁ w₂ :=
      ⟨fun z _ => (d0 z).hasDerivWithinAt, fun z _ => (d1 z).hasDerivWithinAt, d2, z0, z1⟩
    obtain ⟨m1, l1⟩ := weyl_A0_w1 hk hs hl
    obtain ⟨p2, a2, dec⟩ := weyl_A0_w2 hk hs hl
    exact ⟨w, w₁, w₂, d0, d1, fun z hz => (d2 z hz).congr_deriv (by ring), z0, z1, hl,
      m1.monotoneOn, fun z hz => (l1 z hz).le, p2 0 le_rfl, fun z hz => (p2 z hz).le, a2, dec⟩
  · obtain ⟨g, hg, hfix⟩ := exists_fixed hpos.le
    obtain ⟨w, w₁, w₂, h, _⟩ := hg.weyl_theorem_of_fixed hpos (fun z _ => hfix z) k hk
    exact ⟨w, w₁, w₂, h⟩

/-- **Explicit bounds for `w''(0)`** (Weyl's appraisal `c < β < 1 + √(π/2c)`, p. 405, and
`w''(0) = α k^{3/2}`, `α = β^{-3/2}`): for `λ > 0` the solution of Weyl's theorem can be
chosen such that, with `K = c₁ + c₂ = 1 + 2λ/3 + max (1 - 2λ) 0`,

  `k³ / (1 + √(π K / 2))³ ≤ w''(0)² ≤ (2K)³ k³`. -/
theorem weyl_theorem_bounds {lam : ℝ} (hlam : 0 < lam) (k : ℝ) (hk : 0 < k) :
    ∃ w w₁ w₂ : ℝ → ℝ, IsWeylSol lam k w w₁ w₂ ∧
      k ^ 3 ≤ w₂ 0 ^ 2 * (1 + Real.sqrt (Real.pi * (c1 lam + c2 lam) / 2)) ^ 3 ∧
      w₂ 0 ^ 2 ≤ (2 * (c1 lam + c2 lam)) ^ 3 * k ^ 3 := by
  obtain ⟨g, hg, hfix'⟩ := exists_fixed hlam.le
  have hfix : ∀ z, 0 ≤ z → PhiL lam g z = g z := fun z _ => hfix' z
  obtain ⟨w, w₁, w₂, h, he⟩ := hg.weyl_theorem_of_fixed hlam hfix k hk
  have hc2 : 0 ≤ c2 lam := le_max_right _ _
  have hc1 : 0 < c1 lam := by
    unfold c1
    positivity
  set K := c1 lam + c2 lam with hK
  have hK0 : 0 < K := by linarith
  have hγ := hg.F1_one_pos hlam hfix
  have hγK := hg.F1_one_ge hlam hfix
  rw [← hK] at hγK
  have hβ := hg.betaL_pos hlam hfix
  -- upper bound for `β`
  have hsq : Real.sqrt (Real.pi / F1 g 1) / 2 ≤ Real.sqrt (Real.pi * K / 2) := by
    have h1 : Real.pi / F1 g 1 ≤ Real.pi * (2 * K) := by
      rw [div_le_iff₀ hγ]
      have h2 : 1 ≤ 2 * K * F1 g 1 := by
        have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).1 hγK
        linarith
      nlinarith [Real.pi_pos]
    have h3 : Real.sqrt (Real.pi * (2 * K)) = 2 * Real.sqrt (Real.pi * K / 2) := by
      rw [show Real.pi * (2 * K) = 2 ^ 2 * (Real.pi * K / 2) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have := Real.sqrt_le_sqrt h1
    rw [h3] at this
    linarith
  have hβle : InG.betaL g ≤ 1 + Real.sqrt (Real.pi * K / 2) :=
    (hg.betaL_le hlam hfix).trans (by linarith)
  have hβge : 1 / (2 * K) ≤ InG.betaL g := hγK.trans (hg.betaL_ge hlam hfix)
  refine ⟨w, w₁, w₂, h, ?_, ?_⟩
  · rw [← he]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβ.le hβle 3) (sq_nonneg _)
  · have h1 : 1 ≤ 2 * K * InG.betaL g := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).1 hβge
      linarith
    have h2 : (1 : ℝ) ≤ (2 * K * InG.betaL g) ^ 3 := one_le_pow₀ h1
    calc w₂ 0 ^ 2 ≤ w₂ 0 ^ 2 * (2 * K * InG.betaL g) ^ 3 := le_mul_of_one_le_right (sq_nonneg _) h2
      _ = (2 * K) ^ 3 * (w₂ 0 ^ 2 * InG.betaL g ^ 3) := by ring
      _ = (2 * K) ^ 3 * k ^ 3 := by rw [he]

end Blasius

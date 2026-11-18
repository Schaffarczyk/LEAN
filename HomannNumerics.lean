/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Homann's problem `λ = 1/2`: the constant `q₂` is `< 1` (§5)

Reference: H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
Annals of Mathematics 43 (1942), 381–407, pp. 396–398.

Weyl shows `q₂ < 0.76` by a numerical estimate of two integrals.  We prove the weaker bound
`q₂ ≤ 9/10`, which is all that is needed for convergence and uniqueness, by a different
argument that needs no numerical integration:

* `B = ∫₀^∞ e^{-z³/3} dz ≥ 1`, hence `g₂(z) ≥ 1 - z`;
* therefore `G₂' = 2 J² g₂ ≥ D` with `D(z) = z² - z³/3` and `D(z) = z - 1/3` for `z ≥ 1`;
* with `φ(z) = 4z/5 + z³/15` one has `φ D - φ' ≥ z³/3 - 9/10` on `[0, ∞)`, so that
  `φ e^{-G₂} + ∫₀ᶻ e^{-G₂} (ζ³/3 - 9/10) dζ` is non-increasing; as it vanishes at `0`,
  `∫₀^∞ e^{-G₂} z³/3 ≤ (9/10) ∫₀^∞ e^{-G₂}`.

Main results: `q2_le : q₂ ≤ 9/10` and `psi_fixed_unique'` (the equation `g = Ψ{g}` has at
most one solution).
-/
import Homann

open Set Filter Topology MeasureTheory

noncomputable section

namespace Blasius

namespace Homann

lemma le_of_deriv_nonneg {F F' : ℝ → ℝ} {z : ℝ} (hz : 0 ≤ z)
    (hF : ∀ x, 0 ≤ x → x ≤ z → HasDerivAt F (F' x) x) (h : ∀ x, 0 ≤ x → x ≤ z → 0 ≤ F' x) :
    F 0 ≤ F z :=
  monotoneOn_Icc_of_hasDerivAt hF h (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz

lemma eG_one (z : ℝ) : eG (fun _ => 1) z = Real.exp (-(z ^ 3 / 3)) := by
  unfold eG
  rw [K_const]
  congr 1
  ring

/-- `B = ∫₀^∞ e^{-z³/3} dz ≥ 1`. -/
lemma one_le_B : 1 ≤ Hinf fun _ => 1 := by
  have h := le_of_deriv_nonneg (F := fun z => H1 (fun _ => 1) z - (z - z ^ 4 / 12))
    (F' := fun z => eG (fun _ => 1) z - (1 - z ^ 3 / 3)) (z := 7 / 5) (by norm_num)
    (fun x _ _ => by
      have h1 : HasDerivAt (fun z : ℝ => z - z ^ 4 / 12) (1 - x ^ 3 / 3) x := by
        have := (hasDerivAt_id x).sub (((hasDerivAt_id x).pow 4).div_const 12)
        deriv_conv this
        simp only [id]
        ring
      exact (hasDerivAt_H1 continuous_const x).sub h1)
    (fun x _ _ => by
      rw [eG_one]
      linarith [Real.add_one_le_exp (-(x ^ 3 / 3))])
  simp only [H1, J_apply_zero] at h
  have h2 := adm_one.H1_le (z := 7 / 5) (by norm_num)
  simp only [H1] at h2
  norm_num at h
  linarith

lemma H1_one_le {z : ℝ} (hz : 0 ≤ z) : H1 (fun _ => 1) z ≤ z := by
  have := J_mono (u := eG fun _ => 1) (v := fun _ => 1) (eG_continuous continuous_const)
    continuous_const (fun t _ => by
      rw [eG_one]
      exact Real.exp_le_one_iff.2 (by
        have : (0 : ℝ) ≤ t ^ 3 / 3 := by positivity
        linarith)) hz
  rw [J_const] at this
  simpa [H1] using this

/-- `g₂(z) ≥ 1 - z`. -/
lemma g2_ge {z : ℝ} (hz : 0 ≤ z) : 1 - z ≤ g2 z := by
  have hB := one_le_B
  have h1 := H1_one_le hz
  have h0 : 0 ≤ H1 (fun _ => 1) z := Adm.H1_nonneg hz
  have h2 : H1 (fun _ => 1) z / Hinf (fun _ => 1) ≤ H1 (fun _ => 1) z :=
    div_le_self h0 hB
  rw [g2, Adm.Psi_eq hz, psi]
  linarith

lemma g2_nonneg (z : ℝ) : 0 ≤ g2 z := (g2_mem z).1.le

lemma Jg2_ge {z : ℝ} (hz : 0 ≤ z) : z - z ^ 2 / 2 ≤ J g2 z := by
  have h := le_of_deriv_nonneg (F := fun z => J g2 z - (z - z ^ 2 / 2))
    (F' := fun z => g2 z - (1 - z)) hz
    (fun x _ _ => by
      have h1 : HasDerivAt (fun z : ℝ => z - z ^ 2 / 2) (1 - x) x := by
        have := (hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2).div_const 2)
        deriv_conv this
        simp only [id]
        ring
      exact (J_hasDerivAt g2_continuous x).sub h1)
    (fun x hx _ => sub_nonneg.2 (g2_ge hx))
  simp only [J_apply_zero] at h
  norm_num at h
  linarith

lemma Jg2_ge_half {z : ℝ} (hz : 1 ≤ z) : 1 / 2 ≤ J g2 z := by
  have hm := monotoneOn_Icc_of_hasDerivAt (F := J g2) (s := 0) (t := z)
    (fun u _ _ => J_hasDerivAt g2_continuous u) (fun u _ _ => g2_nonneg u)
  have := hm ⟨zero_le_one, hz⟩ (right_mem_Icc.2 (zero_le_one.trans hz)) hz
  have h1 := Jg2_ge (z := 1) zero_le_one
  norm_num at h1
  linarith

lemma JJg2_ge {z : ℝ} (hz : 0 ≤ z) : z ^ 2 / 2 - z ^ 3 / 6 ≤ J (J g2) z := by
  have h := le_of_deriv_nonneg (F := fun z => J (J g2) z - (z ^ 2 / 2 - z ^ 3 / 6))
    (F' := fun z => J g2 z - (z - z ^ 2 / 2)) hz
    (fun x _ _ => by
      have h1 : HasDerivAt (fun z : ℝ => z ^ 2 / 2 - z ^ 3 / 6) (x - x ^ 2 / 2) x := by
        have := (((hasDerivAt_id x).pow 2).div_const 2).sub
          (((hasDerivAt_id x).pow 3).div_const 6)
        deriv_conv this
        simp only [id]
        ring
      exact (J_hasDerivAt (J_continuous g2_continuous) x).sub h1)
    (fun x hx _ => sub_nonneg.2 (Jg2_ge hx))
  simp only [J_apply_zero] at h
  norm_num at h
  linarith

lemma JJg2_ge' {z : ℝ} (hz : 1 ≤ z) : z / 2 - 1 / 6 ≤ J (J g2) z := by
  have hm := monotoneOn_Icc_of_hasDerivAt (F := fun x => J (J g2) x - x / 2)
    (F' := fun x => J g2 x - 1 / 2) (s := 1) (t := z)
    (fun x _ _ => by
      have h1 : HasDerivAt (fun z : ℝ => z / 2) (1 / 2) x := (hasDerivAt_id x).div_const 2
      exact (J_hasDerivAt (J_continuous g2_continuous) x).sub h1)
    (fun x hx _ => sub_nonneg.2 (Jg2_ge_half hx))
  have := hm (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
  have h1 := JJg2_ge (z := 1) zero_le_one
  norm_num at h1
  simp only at this
  linarith

lemma hasDerivAt_eG {g : ℝ → ℝ} (hg : Continuous g) (z : ℝ) :
    HasDerivAt (eG g) (eG g z * -(2 * J (J g) z)) z :=
  (((hasDerivAt_K hg z).const_mul 2).neg).exp

/-- The polynomial inequality behind `q₂ ≤ 9/10`, for `z ≤ 1`. -/
lemma cert1 {z d : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hd : z ^ 2 / 2 - z ^ 3 / 6 ≤ d) :
    z ^ 3 / 3 - 9 / 10 ≤ (4 * z / 5 + z ^ 3 / 15) * (2 * d) - (4 / 5 + z ^ 2 / 5) := by
  have hφ : 0 ≤ 4 * z / 5 + z ^ 3 / 15 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hd hφ
  have key : z ^ 3 / 3 - 9 / 10
      ≤ (4 * z / 5 + z ^ 3 / 15) * (2 * (z ^ 2 / 2 - z ^ 3 / 6)) - (4 / 5 + z ^ 2 / 5) := by
    have a1 : 0 ≤ 1 - z := by linarith
    have a2 : 0 ≤ z ^ 3 := by positivity
    have a3 : 0 ≤ z ^ 5 * (1 - z) := by positivity
    have a4 : 0 ≤ z ^ 3 * (1 - z) := by positivity
    have a5 : 0 ≤ z ^ 2 * (1 - z) := by positivity
    nlinarith [sq_nonneg (z - 2 / 3), mul_nonneg hz (sq_nonneg (z - 2 / 3))]
  linarith

/-- The polynomial inequality behind `q₂ ≤ 9/10`, for `z ≥ 1`. -/
lemma cert2 {z d : ℝ} (hz1 : 1 ≤ z) (hd : z / 2 - 1 / 6 ≤ d) :
    z ^ 3 / 3 - 9 / 10 ≤ (4 * z / 5 + z ^ 3 / 15) * (2 * d) - (4 / 5 + z ^ 2 / 5) := by
  have hz : 0 ≤ z := by linarith
  have hφ : 0 ≤ 4 * z / 5 + z ^ 3 / 15 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hd hφ
  have key : z ^ 3 / 3 - 9 / 10
      ≤ (4 * z / 5 + z ^ 3 / 15) * (2 * (z / 2 - 1 / 6)) - (4 / 5 + z ^ 2 / 5) := by
    obtain ⟨t, rfl⟩ : ∃ t, z = 1 + t := ⟨z - 1, by ring⟩
    have ht : 0 ≤ t := by linarith
    nlinarith [sq_nonneg (t ^ 2 - t), sq_nonneg (t - 1), mul_nonneg ht (sq_nonneg (t - 1)),
      sq_nonneg t]
  linarith

/-- **Weyl's §5** (in the weaker form sufficient for §4): `q₂ ≤ 9/10 < 1`. -/
theorem q2_le : q2 ≤ 9 / 10 := by
  have hc := g2_continuous
  have key : ∀ R, 0 ≤ R → NR g2 R ≤ 9 / 10 * Hinf g2 := by
    intro R hR
    have hanti := antitoneOn_Icc_of_hasDerivAt
      (F := fun z => (4 * z / 5 + z ^ 3 / 15) * eG g2 z + NR g2 z - 9 / 10 * H1 g2 z)
      (F' := fun z => (4 / 5 + z ^ 2 / 5) * eG g2 z
        + (4 * z / 5 + z ^ 3 / 15) * (eG g2 z * -(2 * J (J g2) z))
        + eG g2 z * (z ^ 3 / 3) - 9 / 10 * eG g2 z) (s := 0) (t := R)
      (fun x _ _ => by
        have h1 : HasDerivAt (fun z : ℝ => 4 * z / 5 + z ^ 3 / 15) (4 / 5 + x ^ 2 / 5) x := by
          have := (((hasDerivAt_id x).const_mul 4).div_const 5).add
            (((hasDerivAt_id x).pow 3).div_const 15)
          deriv_conv this
          simp only [id]
          ring
        exact ((h1.mul (hasDerivAt_eG hc x)).add (hasDerivAt_NR hc x)).sub
          ((hasDerivAt_H1 hc x).const_mul _))
      (fun x hx _ => by
        have he := eG_pos g2 x
        have hcert : x ^ 3 / 3 - 9 / 10
            ≤ (4 * x / 5 + x ^ 3 / 15) * (2 * J (J g2) x) - (4 / 5 + x ^ 2 / 5) := by
          rcases le_total x 1 with h | h
          · exact cert1 hx h (JJg2_ge hx)
          · exact cert2 h (JJg2_ge' h)
        have := mul_nonneg he.le (sub_nonneg.2 hcert)
        nlinarith)
    have := hanti (left_mem_Icc.2 hR) (right_mem_Icc.2 hR) hR
    simp only [NR, H1, J_apply_zero] at this
    norm_num at this
    have h2 : 0 ≤ (4 * R / 5 + R ^ 3 / 15) * eG g2 R :=
      mul_nonneg (by positivity) (eG_pos g2 R).le
    have h3 := adm_g2.H1_le hR
    simp only [NR, H1] at h3 ⊢
    linarith
  have hN : N3 g2 ≤ 9 / 10 * Hinf g2 :=
    le_of_tendsto adm_g2.NR_tendsto ((eventually_ge_atTop 0).mono key)
  have hH := adm_g2.Hinf_pos
  rw [q2, qq, div_le_iff₀ hH]
  exact hN

theorem q2_lt_one : q2 < 1 := lt_of_le_of_lt q2_le (by norm_num)

/-- A solution of `g = Ψ{g}` lies above `g₂ = Ψ{1}`. -/
lemma g2_le_of_fixed {u : ℝ → ℝ} (hu : Adm u) (fu : ∀ z, 0 ≤ z → psi u z = u z) {t : ℝ}
    (ht : 0 ≤ t) : g2 t ≤ u t := by
  rw [g2, Adm.Psi_eq ht, ← fu t ht]
  exact psi_antitone hu adm_one hu.le_one ht

/-- **Uniqueness for Homann's problem in Weyl's form (28)**: the equation `g = Ψ{g}` has at
most one solution among the continuous `g ≤ 1` to which `Ψ` is applicable. -/
theorem psi_fixed_unique' {u v : ℝ → ℝ} (hu : Adm u) (hv : Adm v)
    (fu : ∀ z, 0 ≤ z → psi u z = u z) (fv : ∀ z, 0 ≤ z → psi v z = v z) {z : ℝ} (hz : 0 ≤ z) :
    u z = v z :=
  psi_fixed_unique q2_lt_one hu.cont hv.cont (fun _ ht => g2_le_of_fixed hu fu ht) hu.le_one
    (fun _ ht => g2_le_of_fixed hv fv ht) hv.le_one fu fv hz

end Homann

end Blasius

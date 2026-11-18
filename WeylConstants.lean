/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Numerical constants in Weyl's paper

Reference: H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
Annals of Mathematics 43 (1942), 381–407, pp. 388 and 396–398.

* `exp_alt`: the partial sums of the exponential series enclose `e^{-x}` alternately for
  `x ≥ 0`;
* `B_ge`: `B = ∫₀^∞ e^{-z³/3} dz ≥ 1.287` (Weyl: `B = 1.288`), by integrating a partial
  sum of the exponential series over `[0, 2.7]`;
* `weyl_A0_alpha`: for the Blasius problem `w''(0) < 0.685 k^{3/2}` (p. 388).  Weyl states
  `α < 0.684`; this does not follow from `β ≥ B`, because `B^{-3/2} = 0.68419…`.
* `q2_le_three_quarters`: `q₂ ≤ 3/4`, which contains Weyl's `q₂ < 0.76` (p. 398).  The
  proof is the certificate argument of `HomannNumerics.lean` with `B ≥ 7/6` and
  `φ(z) = 2z/3 + z³/16`.
-/
import HomannNumerics

open Set Filter Topology MeasureTheory Finset

noncomputable section

namespace Blasius

/-! ## Alternating bounds for the exponential series -/

/-- Partial sum of the series of `e^{-x}`. -/
def S (n : ℕ) (x : ℝ) : ℝ := ∑ i ∈ range n, (-1) ^ i / (i.factorial : ℝ) * x ^ i

lemma S_continuous (n : ℕ) : Continuous (S n) := by
  unfold S
  fun_prop

lemma J_sum (n : ℕ) (c : ℕ → ℝ) (e : ℕ → ℕ) (z : ℝ) :
    J (fun t => ∑ i ∈ range n, c i * t ^ e i) z
      = ∑ i ∈ range n, c i / ((e i : ℝ) + 1) * z ^ (e i + 1) := by
  unfold J
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (by fun_prop : Continuous fun t : ℝ => c i * t ^ e i).intervalIntegrable _ _]
  exact sum_congr rfl fun i _ => J_monomial (c i) (e i) z

lemma S_succ (n : ℕ) (x : ℝ) : S (n + 1) x = 1 - J (S n) x := by
  have h := J_sum n (fun i => (-1) ^ i / (i.factorial : ℝ)) (fun i => i) x
  have e : J (S n) x = ∑ i ∈ range n, (-1) ^ i / (i.factorial : ℝ) / ((i : ℝ) + 1) * x ^ (i + 1) :=
    h
  rw [e]
  unfold S
  rw [sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  rw [sub_eq_add_neg, add_comm, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [Nat.factorial_succ]
  push_cast
  have h1 : (i.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (i : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- For `x ≥ 0` the partial sums of the exponential series lie alternately above and below
`e^{-x}`. -/
theorem exp_alt (n : ℕ) : ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1) ^ n * (Real.exp (-x) - S n x) := by
  induction n with
  | zero =>
    intro x _
    simp only [S, range_zero, sum_empty, pow_zero, one_mul, sub_zero]
    exact (Real.exp_pos _).le
  | succ n ih =>
    intro x hx
    have h := Homann.le_of_deriv_nonneg
      (F := fun y => (-1) ^ (n + 1) * (Real.exp (-y) - (1 - J (S n) y)))
      (F' := fun y => (-1) ^ n * (Real.exp (-y) - S n y)) hx
      (fun y _ _ => by
        have h1 := (hasDerivAt_id y).neg.exp
        have h2 := (J_hasDerivAt (S_continuous n) y).const_sub 1
        have h3 := (h1.sub h2).const_mul ((-1 : ℝ) ^ (n + 1))
        deriv_conv h3
        simp only [Pi.neg_apply, id]
        rw [pow_succ]
        ring)
      (fun y hy _ => ih y hy)
    simp only [J_apply_zero, neg_zero, Real.exp_zero, sub_zero, sub_self, mul_zero] at h
    rw [S_succ]
    exact h

lemma S_le_exp (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : S (2 * m) x ≤ Real.exp (-x) := by
  have := exp_alt (2 * m) x hx
  rw [pow_mul] at this
  norm_num at this
  linarith

namespace Homann

/-- Lower bound for `∫₀ᴿ e^{-z³/3} dz` by a partial sum. -/
lemma H1_one_ge (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∑ i ∈ range (2 * m),
        (-1) ^ i / (i.factorial : ℝ) / 3 ^ i / (((3 * i : ℕ) : ℝ) + 1) * R ^ (3 * i + 1)
      ≤ H1 (fun _ => 1) R := by
  have hc : Continuous fun t : ℝ =>
      ∑ i ∈ range (2 * m), (-1) ^ i / (i.factorial : ℝ) / 3 ^ i * t ^ (3 * i) := by
    fun_prop
  have := J_mono hc (eG_continuous (g := fun _ => 1) continuous_const) (fun t ht => by
    rw [eG_one]
    have h1 := S_le_exp m (x := t ^ 3 / 3) (by positivity)
    have h2 : S (2 * m) (t ^ 3 / 3)
        = ∑ i ∈ range (2 * m), (-1) ^ i / (i.factorial : ℝ) / 3 ^ i * t ^ (3 * i) := by
      unfold S
      refine sum_congr rfl fun i _ => ?_
      rw [div_pow, pow_mul]
      ring
    linarith) hR
  rw [J_sum (2 * m) (fun i => (-1) ^ i / (i.factorial : ℝ) / 3 ^ i) (fun i => 3 * i)] at this
  exact this

lemma Hinf_one : Hinf (fun _ => 1) = ∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3)) := by
  unfold Hinf
  simp only [eG_one]

/-- `B ≥ 7/6`. -/
lemma B_ge_76 : 7 / 6 ≤ Hinf fun _ => 1 := by
  have h := H1_one_ge 2 (R := 3 / 2) (by norm_num)
  have h2 := adm_one.H1_le (z := 3 / 2) (by norm_num)
  have key : (7 / 6 : ℝ) ≤ ∑ i ∈ range (2 * 2),
      (-1) ^ i / (i.factorial : ℝ) / 3 ^ i / (((3 * i : ℕ) : ℝ) + 1) * (3 / 2) ^ (3 * i + 1) := by
    norm_num [sum_range_succ, Nat.factorial]
  linarith

/-- `B = ∫₀^∞ e^{-z³/3} dz ≥ 1.287` (Weyl, p. 388 and p. 396: `B = 1.288`). -/
theorem B_ge : 1287 / 1000 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3)) := by
  have h := H1_one_ge 13 (R := 27 / 10) (by norm_num)
  have h2 := adm_one.H1_le (z := 27 / 10) (by norm_num)
  have key : (1287 / 1000 : ℝ) ≤ ∑ i ∈ range (2 * 13),
      (-1) ^ i / (i.factorial : ℝ) / 3 ^ i / (((3 * i : ℕ) : ℝ) + 1)
        * (27 / 10) ^ (3 * i + 1) := by
    norm_num [sum_range_succ, Nat.factorial]
  rw [← Hinf_one]
  linarith

end Homann

/-- **Weyl, p. 388**: for the Blasius problem `w''' + 2ww'' = 0`, `w(0) = w'(0) = 0`,
`w'(∞) = k`, the constant `α = w''(0) / k^{3/2}` satisfies `α < 0.685`. -/
theorem weyl_A0_alpha {k : ℝ} {w w₁ w₂ : ℝ → ℝ} (hk : 0 < k) (h : IsSol w w₁ w₂)
    (hlim : Tendsto w₁ atTop (𝓝 k)) : w₂ 0 ^ 2 < (685 / 1000) ^ 2 * k ^ 3 := by
  obtain ⟨_, he⟩ := weyl_A0_second_deriv_zero hk h hlim
  have hβ : (1287 / 1000 : ℝ) ≤ β := Homann.B_ge.trans β_ge
  have hb3 : (1287 / 1000 : ℝ) ^ 3 ≤ β ^ 3 := pow_le_pow_left₀ (by norm_num) hβ 3
  have h1 : w₂ 0 ^ 2 * (1287 / 1000 : ℝ) ^ 3 ≤ k ^ 3 := by
    rw [← he]
    exact mul_le_mul_of_nonneg_left hb3 (sq_nonneg _)
  have hk3 : 0 < k ^ 3 := by positivity
  have e : (1 : ℝ) < (685 / 1000) ^ 2 * (1287 / 1000) ^ 3 := by norm_num
  by_contra hc
  push Not at hc
  have h2 := mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ (1287 / 1000) ^ 3 by norm_num)
  nlinarith [mul_pos (sub_pos.2 e) hk3]

namespace Homann

/-! ## `q₂ ≤ 3/4` -/

lemma g2_ge' {z : ℝ} (hz : 0 ≤ z) : 1 - 6 / 7 * z ≤ g2 z := by
  have hB := B_ge_76
  have h1 := H1_one_le hz
  have h0 : 0 ≤ H1 (fun _ => 1) z := Adm.H1_nonneg hz
  have h2 : H1 (fun _ => 1) z / Hinf (fun _ => 1) ≤ H1 (fun _ => 1) z / (7 / 6) :=
    div_le_div_of_nonneg_left h0 (by norm_num) hB
  rw [g2, Adm.Psi_eq hz, psi]
  linarith

lemma Jg2_ge' {z : ℝ} (hz : 0 ≤ z) : z - 3 / 7 * z ^ 2 ≤ J g2 z := by
  have h := le_of_deriv_nonneg (F := fun z => J g2 z - (z - 3 / 7 * z ^ 2))
    (F' := fun z => g2 z - (1 - 6 / 7 * z)) hz
    (fun x _ _ => by
      have h1 : HasDerivAt (fun z : ℝ => z - 3 / 7 * z ^ 2) (1 - 6 / 7 * x) x := by
        have := (hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2).const_mul (3 / 7))
        deriv_conv this
        simp only [id]
        ring
      exact (J_hasDerivAt g2_continuous x).sub h1)
    (fun x hx _ => sub_nonneg.2 (g2_ge' hx))
  simp only [J_apply_zero] at h
  norm_num at h
  linarith

lemma Jg2_ge_712 {z : ℝ} (hz : 7 / 6 ≤ z) : 7 / 12 ≤ J g2 z := by
  have hm := monotoneOn_Icc_of_hasDerivAt (F := J g2) (s := 0) (t := z)
    (fun u _ _ => J_hasDerivAt g2_continuous u) (fun u _ _ => g2_nonneg u)
  have := hm ⟨by norm_num, hz⟩ (right_mem_Icc.2 (by linarith)) hz
  have h1 := Jg2_ge' (z := 7 / 6) (by norm_num)
  norm_num at h1
  linarith

lemma JJg2_ge_a {z : ℝ} (hz : 0 ≤ z) : z ^ 2 / 2 - z ^ 3 / 7 ≤ J (J g2) z := by
  have h := le_of_deriv_nonneg (F := fun z => J (J g2) z - (z ^ 2 / 2 - z ^ 3 / 7))
    (F' := fun z => J g2 z - (z - 3 / 7 * z ^ 2)) hz
    (fun x _ _ => by
      have h1 : HasDerivAt (fun z : ℝ => z ^ 2 / 2 - z ^ 3 / 7) (x - 3 / 7 * x ^ 2) x := by
        have := (((hasDerivAt_id x).pow 2).div_const 2).sub
          (((hasDerivAt_id x).pow 3).div_const 7)
        deriv_conv this
        simp only [id]
        ring
      exact (J_hasDerivAt (J_continuous g2_continuous) x).sub h1)
    (fun x hx _ => sub_nonneg.2 (Jg2_ge' hx))
  simp only [J_apply_zero] at h
  norm_num at h
  linarith

lemma JJg2_ge_b {z : ℝ} (hz : 7 / 6 ≤ z) : 7 / 12 * z - 49 / 216 ≤ J (J g2) z := by
  have hm := monotoneOn_Icc_of_hasDerivAt (F := fun x => J (J g2) x - 7 / 12 * x)
    (F' := fun x => J g2 x - 7 / 12) (s := 7 / 6) (t := z)
    (fun x _ _ => by
      have h1 : HasDerivAt (fun z : ℝ => 7 / 12 * z) (7 / 12) x := by
        simpa using (hasDerivAt_id x).const_mul (7 / 12 : ℝ)
      exact (J_hasDerivAt (J_continuous g2_continuous) x).sub h1)
    (fun x hx _ => sub_nonneg.2 (Jg2_ge_712 hx))
  have := hm (left_mem_Icc.2 hz) (right_mem_Icc.2 hz) hz
  have h1 := JJg2_ge_a (z := 7 / 6) (by norm_num)
  norm_num at h1
  simp only at this
  linarith

lemma cert1' {z d : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 7 / 6) (hd : z ^ 2 / 2 - z ^ 3 / 7 ≤ d) :
    z ^ 3 / 3 - 3 / 4 ≤ (2 * z / 3 + z ^ 3 / 16) * (2 * d) - (2 / 3 + 3 * z ^ 2 / 16) := by
  have hφ : 0 ≤ 2 * z / 3 + z ^ 3 / 16 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hd hφ
  have key : z ^ 3 / 3 - 3 / 4
      ≤ (2 * z / 3 + z ^ 3 / 16) * (2 * (z ^ 2 / 2 - z ^ 3 / 7)) - (2 / 3 + 3 * z ^ 2 / 16) := by
    have a1 : 0 ≤ 7 / 6 - z := by linarith
    have a3 : 0 ≤ z ^ 5 * (7 / 6 - z) := by positivity
    have a4 : 0 ≤ z ^ 3 * (7 / 6 - z) := by positivity
    have a5 : 0 ≤ z ^ 2 * (7 / 6 - z) := by positivity
    have a6 : 0 ≤ z ^ 4 * (7 / 6 - z) := by positivity
    have a7 : 0 ≤ z * (7 / 6 - z) := by positivity
    nlinarith [sq_nonneg (z - 2 / 3), mul_nonneg hz (sq_nonneg (z - 2 / 3)),
      mul_nonneg hz (sq_nonneg (z - 1)), sq_nonneg (z - 1)]
  linarith

lemma cert2' {z d : ℝ} (hz1 : 7 / 6 ≤ z) (hd : 7 / 12 * z - 49 / 216 ≤ d) :
    z ^ 3 / 3 - 3 / 4 ≤ (2 * z / 3 + z ^ 3 / 16) * (2 * d) - (2 / 3 + 3 * z ^ 2 / 16) := by
  have hz : 0 ≤ z := by linarith
  have hφ : 0 ≤ 2 * z / 3 + z ^ 3 / 16 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hd hφ
  have key : z ^ 3 / 3 - 3 / 4
      ≤ (2 * z / 3 + z ^ 3 / 16) * (2 * (7 / 12 * z - 49 / 216)) - (2 / 3 + 3 * z ^ 2 / 16) := by
    obtain ⟨t, rfl⟩ : ∃ t, z = 7 / 6 + t := ⟨z - 7 / 6, by ring⟩
    have ht : 0 ≤ t := by linarith
    nlinarith [sq_nonneg (t ^ 2 - t), sq_nonneg (t - 1), mul_nonneg ht (sq_nonneg (t - 1)),
      sq_nonneg t, sq_nonneg (t ^ 2 - 1), mul_nonneg ht (sq_nonneg t)]
  linarith

/-- **Weyl's §5**: `q₂ ≤ 3/4` (Weyl: `q₂ < 0.76`). -/
theorem q2_le_three_quarters : q2 ≤ 3 / 4 := by
  have hc := g2_continuous
  have key : ∀ R, 0 ≤ R → NR g2 R ≤ 3 / 4 * Hinf g2 := by
    intro R hR
    have hanti := antitoneOn_Icc_of_hasDerivAt
      (F := fun z => (2 * z / 3 + z ^ 3 / 16) * eG g2 z + NR g2 z - 3 / 4 * H1 g2 z)
      (F' := fun z => (2 / 3 + 3 * z ^ 2 / 16) * eG g2 z
        + (2 * z / 3 + z ^ 3 / 16) * (eG g2 z * -(2 * J (J g2) z))
        + eG g2 z * (z ^ 3 / 3) - 3 / 4 * eG g2 z) (s := 0) (t := R)
      (fun x _ _ => by
        have h1 : HasDerivAt (fun z : ℝ => 2 * z / 3 + z ^ 3 / 16)
            (2 / 3 + 3 * x ^ 2 / 16) x := by
          have := (((hasDerivAt_id x).const_mul 2).div_const 3).add
            (((hasDerivAt_id x).pow 3).div_const 16)
          deriv_conv this
          simp only [id]
          ring
        exact ((h1.mul (hasDerivAt_eG hc x)).add (hasDerivAt_NR hc x)).sub
          ((hasDerivAt_H1 hc x).const_mul _))
      (fun x hx _ => by
        have he := eG_pos g2 x
        have hcert : x ^ 3 / 3 - 3 / 4
            ≤ (2 * x / 3 + x ^ 3 / 16) * (2 * J (J g2) x) - (2 / 3 + 3 * x ^ 2 / 16) := by
          rcases le_total x (7 / 6) with h | h
          · exact cert1' hx h (JJg2_ge_a hx)
          · exact cert2' h (JJg2_ge_b h)
        have := mul_nonneg he.le (sub_nonneg.2 hcert)
        nlinarith)
    have := hanti (left_mem_Icc.2 hR) (right_mem_Icc.2 hR) hR
    simp only [NR, H1, J_apply_zero] at this
    norm_num at this
    have h2 : 0 ≤ (2 * R / 3 + R ^ 3 / 16) * eG g2 R :=
      mul_nonneg (by positivity) (eG_pos g2 R).le
    have h3 := adm_g2.H1_le hR
    simp only [NR, H1] at h3 ⊢
    linarith
  have hN : N3 g2 ≤ 3 / 4 * Hinf g2 :=
    le_of_tendsto adm_g2.NR_tendsto ((eventually_ge_atTop 0).mono key)
  have hH := adm_g2.Hinf_pos
  rw [q2, qq, div_le_iff₀ hH]
  exact hN

end Homann

end Blasius

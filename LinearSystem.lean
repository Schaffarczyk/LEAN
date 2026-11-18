/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Cooperative linear systems `ψ' = a χ`, `χ' = b ψ` on `[0, ∞)`

Preparation for §6 of

  H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
  Annals of Mathematics 43 (1942), 381–407.

Weyl replaces the linear equation (37), `φ'' + 2 f φ' + 2 (1 - 2λ) f' φ = 0`, by the
system (41) for `(φ, φ₁)`, `φ₁ = p (φ' + 2 f φ)`, `p = exp (2 ∫ f)`.  In the variables
`ψ = p φ`, `χ = φ₁ / p` the system (41) reads

  `ψ' = a χ`,   `χ' = b ψ`,   `a = p ≥ 1`,   `b = 4 λ f' / p ≥ 0`,

and Weyl's "Dirichlet integral" identity (43) becomes `(ψ χ)' = a χ² + b ψ² ≥ 0`.

This file treats such systems for arbitrary continuous `a, b`:

* `solψ`, `solχ`: the solution with given initial values (Picard iteration);
* `IsLinOn.eq_zero`, `IsLinOn.unique`: uniqueness when `a, b ≥ 0`;
* `IsLinOn.nonneg`: for `a, b ≥ 0`, non-negative initial values give `ψ ≥ 0`, `χ ≥ χ(0)`;
* `IsLinOn.reverse`: time reversal `t ↦ T - t` maps solutions to solutions of the reversed
  system with `χ` replaced by `-χ`.
-/
import WeylGeneral
import Mathlib.Analysis.Calculus.Deriv.Shift

open Set Filter Topology MeasureTheory
open scoped Nat

noncomputable section

namespace Blasius

/-! ## Auxiliary lemmas -/

lemma monotoneOn_Icc_of_hasDerivAt {F F' : ℝ → ℝ} {s t : ℝ}
    (hF : ∀ x, s ≤ x → x ≤ t → HasDerivAt F (F' x) x)
    (h : ∀ x, s ≤ x → x ≤ t → 0 ≤ F' x) : MonotoneOn F (Icc s t) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc s t)
    (fun x hx => (hF x hx.1 hx.2).continuousAt.continuousWithinAt) (fun x hx => ?_)
    fun x hx => ?_
  · have hx' := interior_subset hx
    exact (hF x hx'.1 hx'.2).differentiableAt.differentiableWithinAt
  · have hx' := interior_subset hx
    rw [(hF x hx'.1 hx'.2).deriv]
    exact h x hx'.1 hx'.2

lemma antitoneOn_Icc_of_hasDerivAt {F F' : ℝ → ℝ} {s t : ℝ}
    (hF : ∀ x, s ≤ x → x ≤ t → HasDerivAt F (F' x) x)
    (h : ∀ x, s ≤ x → x ≤ t → F' x ≤ 0) : AntitoneOn F (Icc s t) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc s t)
    (fun x hx => (hF x hx.1 hx.2).continuousAt.continuousWithinAt) (fun x hx => ?_)
    fun x hx => ?_
  · have hx' := interior_subset hx
    exact (hF x hx'.1 hx'.2).differentiableAt.differentiableWithinAt
  · have hx' := interior_subset hx
    rw [(hF x hx'.1 hx'.2).deriv]
    exact h x hx'.1 hx'.2

lemma eq_of_hasDerivAt_zero {F : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hF : ∀ x, 0 ≤ x → x ≤ t → HasDerivAt F 0 x) : F t = F 0 :=
  constant_of_has_deriv_right_zero
    (fun x hx => (hF x hx.1 hx.2).continuousAt.continuousWithinAt)
    (fun x hx => (hF x hx.1 hx.2.le).hasDerivWithinAt) t (right_mem_Icc.2 ht)

/-- Dominated convergence for the primitive, with a bound on `[0, z]` only. -/
lemma J_tendsto_on {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {z C : ℝ} (hz : 0 ≤ z)
    (hF : ∀ n, Continuous (F n)) (hb : ∀ n t, 0 ≤ t → t ≤ z → |F n t| ≤ C)
    (hlim : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (f t))) :
    Tendsto (fun n => J (F n) z) atTop (𝓝 (J f z)) := by
  unfold J
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    (Eventually.of_forall fun n => (hF n).aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall fun x hx => ?_)
    intervalIntegrable_const (Eventually.of_forall fun x _ => hlim x)
  rw [uIoc_of_le hz] at hx
  rw [Real.norm_eq_abs]
  exact hb n x (le_of_lt hx.1) hx.2

/-! ## Solutions on an interval -/

/-- `(ψ, χ)` solves `ψ' = a χ`, `χ' = b ψ` on `[0, T]`. -/
structure IsLinOn (a b : ℝ → ℝ) (T : ℝ) (ψ χ : ℝ → ℝ) : Prop where
  dψ : ∀ z, 0 ≤ z → z ≤ T → HasDerivAt ψ (a z * χ z) z
  dχ : ∀ z, 0 ≤ z → z ≤ T → HasDerivAt χ (b z * ψ z) z

namespace IsLinOn

variable {a b : ℝ → ℝ} {T : ℝ} {ψ χ ψ₁ χ₁ ψ₂ χ₂ : ℝ → ℝ}

lemma mono {T' : ℝ} (h : IsLinOn a b T ψ χ) (hT : T' ≤ T) : IsLinOn a b T' ψ χ :=
  ⟨fun z h0 h1 => h.dψ z h0 (h1.trans hT), fun z h0 h1 => h.dχ z h0 (h1.trans hT)⟩

/-- Linear combinations of solutions are solutions. -/
lemma comb (h₁ : IsLinOn a b T ψ₁ χ₁) (h₂ : IsLinOn a b T ψ₂ χ₂) (c₁ c₂ : ℝ) :
    IsLinOn a b T (fun z => c₁ * ψ₁ z + c₂ * ψ₂ z) (fun z => c₁ * χ₁ z + c₂ * χ₂ z) := by
  constructor
  · intro z h0 h1
    have := ((h₁.dψ z h0 h1).const_mul c₁).add ((h₂.dψ z h0 h1).const_mul c₂)
    convert this using 1
    ring
  · intro z h0 h1
    have := ((h₁.dχ z h0 h1).const_mul c₁).add ((h₂.dχ z h0 h1).const_mul c₂)
    convert this using 1
    ring

/-- Uniqueness: a solution with vanishing initial values vanishes (for `a, b ≥ 0`). -/
lemma eq_zero (ha : Continuous a) (hb : Continuous b) (ha0 : ∀ z, 0 ≤ a z)
    (hb0 : ∀ z, 0 ≤ b z) (h : IsLinOn a b T ψ χ) (h0 : ψ 0 = 0) (h0' : χ 0 = 0) {z : ℝ}
    (hz : 0 ≤ z) (hzT : z ≤ T) : ψ z = 0 ∧ χ z = 0 := by
  have hab : Continuous fun t => a t + b t := ha.add hb
  have hW : ∀ x, HasDerivAt (fun x => Real.exp (-(J (fun t => a t + b t) x)))
      (Real.exp (-(J (fun t => a t + b t) x)) * (-(a x + b x))) x := fun x =>
    ((J_hasDerivAt hab x).neg).exp
  have hF : ∀ x, 0 ≤ x → x ≤ T →
      HasDerivAt (fun x => (ψ x ^ 2 + χ x ^ 2) * Real.exp (-(J (fun t => a t + b t) x)))
        (-(Real.exp (-(J (fun t => a t + b t) x)) * (a x + b x) * (ψ x - χ x) ^ 2)) x := by
    intro x hx0 hxT
    have := ((((h.dψ x hx0 hxT).pow 2).add ((h.dχ x hx0 hxT).pow 2))).mul (hW x)
    convert this using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.add_apply, Pi.pow_apply]
    ring
  have hanti := antitoneOn_Icc_of_hasDerivAt (s := 0) (t := T) hF fun x hx0 _ => by
    have h1 := Real.exp_pos (-(J (fun t => a t + b t) x))
    have h2 := add_nonneg (ha0 x) (hb0 x)
    have h3 := sq_nonneg (ψ x - χ x)
    have : 0 ≤ Real.exp (-(J (fun t => a t + b t) x)) * (a x + b x) * (ψ x - χ x) ^ 2 := by
      positivity
    linarith
  have hle := hanti (left_mem_Icc.2 (hz.trans hzT)) ⟨hz, hzT⟩ hz
  simp only [h0, h0', J_apply_zero] at hle
  have hpos := Real.exp_pos (-(J (fun t => a t + b t) z))
  have hsum : ψ z ^ 2 + χ z ^ 2 ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have := mul_pos hcon hpos
    norm_num at hle
    linarith
  have h1 : ψ z ^ 2 = 0 := by nlinarith [sq_nonneg (ψ z), sq_nonneg (χ z)]
  have h2 : χ z ^ 2 = 0 := by nlinarith [sq_nonneg (ψ z), sq_nonneg (χ z)]
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- Two solutions with the same initial values coincide (for `a, b ≥ 0`). -/
lemma unique (ha : Continuous a) (hb : Continuous b) (ha0 : ∀ z, 0 ≤ a z)
    (hb0 : ∀ z, 0 ≤ b z) (h₁ : IsLinOn a b T ψ₁ χ₁) (h₂ : IsLinOn a b T ψ₂ χ₂)
    (h0 : ψ₁ 0 = ψ₂ 0) (h0' : χ₁ 0 = χ₂ 0) {z : ℝ} (hz : 0 ≤ z) (hzT : z ≤ T) :
    ψ₁ z = ψ₂ z ∧ χ₁ z = χ₂ z := by
  have := (h₁.comb h₂ 1 (-1)).eq_zero ha hb ha0 hb0 (by simp [h0]) (by simp [h0']) hz hzT
  simp only [one_mul, neg_mul] at this
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- Time reversal. -/
lemma reverse (h : IsLinOn a b T ψ χ) :
    IsLinOn (fun t => a (T - t)) (fun t => b (T - t)) T (fun t => ψ (T - t))
      (fun t => -χ (T - t)) := by
  constructor
  · intro z h0 h1
    have := HasDerivAt.comp_const_sub T z (h.dψ (T - z) (by linarith) (by linarith))
    convert this using 1
    ring
  · intro z h0 h1
    have := (HasDerivAt.comp_const_sub T z (h.dχ (T - z) (by linarith) (by linarith))).neg
    convert this using 1
    ring

end IsLinOn

/-! ## Existence: Picard iteration -/

section Picard

variable (a b : ℝ → ℝ) (ψ0 χ0 : ℝ)

/-- Picard iterates for `ψ = ψ0 + J (a χ)`, `χ = χ0 + J (b ψ)` (arguments clamped at `0`). -/
def pic : ℕ → (ℝ → ℝ) × (ℝ → ℝ)
  | 0 => (fun _ => ψ0, fun _ => χ0)
  | n + 1 => (fun z => ψ0 + J (fun t => a t * (pic n).2 t) (max z 0),
      fun z => χ0 + J (fun t => b t * (pic n).1 t) (max z 0))

variable {a b}

lemma pic_continuous (ha : Continuous a) (hb : Continuous b) :
    ∀ n, Continuous (pic a b ψ0 χ0 n).1 ∧ Continuous (pic a b ψ0 χ0 n).2
  | 0 => ⟨continuous_const, continuous_const⟩
  | n + 1 => by
      obtain ⟨h1, h2⟩ := pic_continuous ha hb n
      have j1 := J_continuous (ha.mul h2)
      have j2 := J_continuous (hb.mul h1)
      constructor
      · show Continuous fun z => ψ0 + J (fun t => a t * (pic a b ψ0 χ0 n).2 t) (max z 0)
        fun_prop
      · show Continuous fun z => χ0 + J (fun t => b t * (pic a b ψ0 χ0 n).1 t) (max z 0)
        fun_prop

lemma pic_max (n : ℕ) (z : ℝ) :
    (pic a b ψ0 χ0 n).1 (max z 0) = (pic a b ψ0 χ0 n).1 z ∧
      (pic a b ψ0 χ0 n).2 (max z 0) = (pic a b ψ0 χ0 n).2 z := by
  cases n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n =>
    constructor
    · show ψ0 + J _ (max (max z 0) 0) = ψ0 + J _ (max z 0)
      rw [max_eq_left (le_max_right z 0)]
    · show χ0 + J _ (max (max z 0) 0) = χ0 + J _ (max z 0)
      rw [max_eq_left (le_max_right z 0)]

lemma pic_nonneg (hψ : 0 ≤ ψ0) (hχ : 0 ≤ χ0) (ha0 : ∀ z, 0 ≤ a z) (hb0 : ∀ z, 0 ≤ b z) :
    ∀ (n : ℕ) (z : ℝ), 0 ≤ (pic a b ψ0 χ0 n).1 z ∧ χ0 ≤ (pic a b ψ0 χ0 n).2 z
  | 0, _ => ⟨hψ, le_rfl⟩
  | n + 1, z => by
      have ih := pic_nonneg hψ hχ ha0 hb0 n
      constructor
      · show 0 ≤ ψ0 + J (fun t => a t * (pic a b ψ0 χ0 n).2 t) (max z 0)
        have := J_nonneg (g := fun t => a t * (pic a b ψ0 χ0 n).2 t)
          (fun t _ => mul_nonneg (ha0 t) (hχ.trans (ih t).2)) (le_max_right z 0)
        linarith
      · show χ0 ≤ χ0 + J (fun t => b t * (pic a b ψ0 χ0 n).1 t) (max z 0)
        have := J_nonneg (g := fun t => b t * (pic a b ψ0 χ0 n).1 t)
          (fun t _ => mul_nonneg (hb0 t) (ih t).1) (le_max_right z 0)
        linarith

lemma pic_diff (ha : Continuous a) (hb : Continuous b) {R M D : ℝ} (hR : 0 ≤ R)
    (hM : ∀ t, 0 ≤ t → t ≤ R → |a t| ≤ M ∧ |b t| ≤ M)
    (hD : ∀ t, 0 ≤ t → t ≤ R →
      |(pic a b ψ0 χ0 1).1 t - (pic a b ψ0 χ0 0).1 t| ≤ D ∧
      |(pic a b ψ0 χ0 1).2 t - (pic a b ψ0 χ0 0).2 t| ≤ D) :
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ R →
      |(pic a b ψ0 χ0 (n + 1)).1 t - (pic a b ψ0 χ0 n).1 t| ≤ D * M ^ n / n ! * t ^ n ∧
      |(pic a b ψ0 χ0 (n + 1)).2 t - (pic a b ψ0 χ0 n).2 t| ≤ D * M ^ n / n ! * t ^ n
  | 0, t, ht, htR => by simpa using hD t ht htR
  | n + 1, t, ht, htR => by
      have ih := pic_diff ha hb hR hM hD n
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 le_rfl hR).1
      obtain ⟨c1, c2⟩ := pic_continuous ψ0 χ0 ha hb (n + 1)
      obtain ⟨c1', c2'⟩ := pic_continuous ψ0 χ0 ha hb n
      have hfac : (((n + 1)! : ℕ) : ℝ) = (n + 1) * (n ! : ℕ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hn : ((n ! : ℕ) : ℝ) ≠ 0 := by positivity
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have key : ∀ (c : ℝ → ℝ) (u v : ℝ → ℝ), Continuous c → Continuous u → Continuous v →
          (∀ s, 0 ≤ s → s ≤ R → |c s| ≤ M) →
          (∀ s, 0 ≤ s → s ≤ R → |u s - v s| ≤ D * M ^ n / n ! * s ^ n) →
          |J (fun s => c s * u s) t - J (fun s => c s * v s) t|
            ≤ D * M ^ (n + 1) / (n + 1)! * t ^ (n + 1) := by
        intro c u v hc hu hv hcM huv
        have := J_sub_le_on (hc.mul hu) (hc.mul hv)
          (d := fun s => M * (D * M ^ n / n !) * s ^ n) (by fun_prop) (a := R)
          (fun s hs hsR => by
            rw [← mul_sub, abs_mul]
            calc |c s| * |u s - v s| ≤ M * (D * M ^ n / n ! * s ^ n) :=
                  mul_le_mul (hcM s hs hsR) (huv s hs hsR) (abs_nonneg _) hM0
              _ = M * (D * M ^ n / n !) * s ^ n := by ring) ht htR
        rw [J_monomial] at this
        refine this.trans (le_of_eq ?_)
        rw [hfac]
        field_simp
        ring
      constructor
      · show |ψ0 + J (fun s => a s * (pic a b ψ0 χ0 (n + 1)).2 s) (max t 0)
            - (ψ0 + J (fun s => a s * (pic a b ψ0 χ0 n).2 s) (max t 0))| ≤ _
        rw [max_eq_left ht, add_sub_add_left_eq_sub]
        exact key a _ _ ha c2 c2' (fun s hs hsR => (hM s hs hsR).1)
          (fun s hs hsR => (ih s hs hsR).2)
      · show |χ0 + J (fun s => b s * (pic a b ψ0 χ0 (n + 1)).1 s) (max t 0)
            - (χ0 + J (fun s => b s * (pic a b ψ0 χ0 n).1 s) (max t 0))| ≤ _
        rw [max_eq_left ht, add_sub_add_left_eq_sub]
        exact key b _ _ hb c1 c1' (fun s hs hsR => (hM s hs hsR).2)
          (fun s hs hsR => (ih s hs hsR).1)

/-- Constants for the estimates on `[0, R]`. -/
lemma pic_bounds (ha : Continuous a) (hb : Continuous b) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M D : ℝ, 0 ≤ M ∧ 0 ≤ D ∧ (∀ t, 0 ≤ t → t ≤ R → |a t| ≤ M ∧ |b t| ≤ M) ∧
      ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ R →
        |(pic a b ψ0 χ0 (n + 1)).1 t - (pic a b ψ0 χ0 n).1 t| ≤ D * M ^ n / n ! * t ^ n ∧
        |(pic a b ψ0 χ0 (n + 1)).2 t - (pic a b ψ0 χ0 n).2 t| ≤ D * M ^ n / n ! * t ^ n := by
  obtain ⟨M, hM⟩ := exists_bound_on (q := fun t => |a t| + |b t|) (by fun_prop) R
  obtain ⟨c1, c2⟩ := pic_continuous ψ0 χ0 ha hb 1
  obtain ⟨c1', c2'⟩ := pic_continuous ψ0 χ0 ha hb 0
  obtain ⟨D, hD⟩ := exists_bound_on
    (q := fun t => |(pic a b ψ0 χ0 1).1 t - (pic a b ψ0 χ0 0).1 t|
      + |(pic a b ψ0 χ0 1).2 t - (pic a b ψ0 χ0 0).2 t|) (by fun_prop) R
  have hM' : ∀ t, 0 ≤ t → t ≤ R → |a t| ≤ M ∧ |b t| ≤ M := fun t h0 h1 => by
    have := hM t h0 h1
    exact ⟨by linarith [abs_nonneg (b t)], by linarith [abs_nonneg (a t)]⟩
  have hD' : ∀ t, 0 ≤ t → t ≤ R →
      |(pic a b ψ0 χ0 1).1 t - (pic a b ψ0 χ0 0).1 t| ≤ D ∧
      |(pic a b ψ0 χ0 1).2 t - (pic a b ψ0 χ0 0).2 t| ≤ D := fun t h0 h1 => by
    have := hD t h0 h1
    exact ⟨by linarith [abs_nonneg ((pic a b ψ0 χ0 1).2 t - (pic a b ψ0 χ0 0).2 t)],
      by linarith [abs_nonneg ((pic a b ψ0 χ0 1).1 t - (pic a b ψ0 χ0 0).1 t)]⟩
  exact ⟨M, D, (abs_nonneg _).trans (hM' 0 le_rfl hR).1, (abs_nonneg _).trans (hD' 0 le_rfl hR).1,
    hM', pic_diff ψ0 χ0 ha hb hR hM' hD'⟩

lemma pic_cauchy (ha : Continuous a) (hb : Continuous b) (z : ℝ) :
    CauchySeq (fun n => (pic a b ψ0 χ0 n).1 z) ∧ CauchySeq (fun n => (pic a b ψ0 χ0 n).2 z) := by
  have hR : 0 ≤ max z 0 := le_max_right _ _
  obtain ⟨M, D, hM0, hD0, -, hdiff⟩ := pic_bounds ψ0 χ0 ha hb hR
  have hsum : Summable fun n : ℕ => D * ((M * max z 0) ^ n / n !) :=
    (Real.summable_pow_div_factorial _).mul_left D
  have e : ∀ n : ℕ, D * M ^ n / n ! * (max z 0) ^ n = D * ((M * max z 0) ^ n / n !) :=
    fun n => by
      rw [mul_pow]
      ring
  constructor
  · refine cauchySeq_of_dist_le_of_summable _ (fun n => ?_) hsum
    rw [Real.dist_eq, abs_sub_comm, ← (pic_max ψ0 χ0 (n + 1) z).1, ← (pic_max ψ0 χ0 n z).1, ← e]
    exact (hdiff n _ hR le_rfl).1
  · refine cauchySeq_of_dist_le_of_summable _ (fun n => ?_) hsum
    rw [Real.dist_eq, abs_sub_comm, ← (pic_max ψ0 χ0 (n + 1) z).2, ← (pic_max ψ0 χ0 n z).2, ← e]
    exact (hdiff n _ hR le_rfl).2

/-- Uniform bound for the iterates on `{z | max z 0 ≤ R}`. -/
lemma pic_bounded (ha : Continuous a) (hb : Continuous b) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∀ (n : ℕ) (x : ℝ), max x 0 ≤ R →
      |(pic a b ψ0 χ0 n).1 x| ≤ C ∧ |(pic a b ψ0 χ0 n).2 x| ≤ C := by
  obtain ⟨M, D, hM0, hD0, -, hdiff⟩ := pic_bounds ψ0 χ0 ha hb hR
  refine ⟨|ψ0| + |χ0| + D * Real.exp (M * R), fun n x hx => ?_⟩
  have h0 : 0 ≤ max x 0 := le_max_right _ _
  have hsum : ∑ k ∈ Finset.range n, D * M ^ k / k ! * (max x 0) ^ k ≤ D * Real.exp (M * R) := by
    have h1 : ∑ k ∈ Finset.range n, D * M ^ k / k ! * (max x 0) ^ k
        = D * ∑ k ∈ Finset.range n, (M * max x 0) ^ k / k ! := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_pow]
      ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ hD0
    refine (Real.sum_le_exp_of_nonneg (mul_nonneg hM0 h0) n).trans ?_
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left hx hM0
  have tele1 : (pic a b ψ0 χ0 n).1 (max x 0) - ψ0
      = ∑ k ∈ Finset.range n,
          ((pic a b ψ0 χ0 (k + 1)).1 (max x 0) - (pic a b ψ0 χ0 k).1 (max x 0)) :=
    (Finset.sum_range_sub (fun k => (pic a b ψ0 χ0 k).1 (max x 0)) n).symm
  have tele2 : (pic a b ψ0 χ0 n).2 (max x 0) - χ0
      = ∑ k ∈ Finset.range n,
          ((pic a b ψ0 χ0 (k + 1)).2 (max x 0) - (pic a b ψ0 χ0 k).2 (max x 0)) :=
    (Finset.sum_range_sub (fun k => (pic a b ψ0 χ0 k).2 (max x 0)) n).symm
  have b1 : |(pic a b ψ0 χ0 n).1 (max x 0) - ψ0| ≤ D * Real.exp (M * R) := by
    rw [tele1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hsum)
    exact Finset.sum_le_sum fun k _ => (hdiff k _ h0 hx).1
  have b2 : |(pic a b ψ0 χ0 n).2 (max x 0) - χ0| ≤ D * Real.exp (M * R) := by
    rw [tele2]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hsum)
    exact Finset.sum_le_sum fun k _ => (hdiff k _ h0 hx).2
  rw [← (pic_max ψ0 χ0 n x).1, ← (pic_max ψ0 χ0 n x).2]
  constructor
  · have := abs_sub_abs_le_abs_sub ((pic a b ψ0 χ0 n).1 (max x 0)) ψ0
    linarith [abs_nonneg χ0]
  · have := abs_sub_abs_le_abs_sub ((pic a b ψ0 χ0 n).2 (max x 0)) χ0
    linarith [abs_nonneg ψ0]

variable (a b)

/-- Limits of the Picard iterates. -/
def linψ (z : ℝ) : ℝ := limUnder atTop (fun n => (pic a b ψ0 χ0 n).1 z)

/-- Limits of the Picard iterates. -/
def linχ (z : ℝ) : ℝ := limUnder atTop (fun n => (pic a b ψ0 χ0 n).2 z)

/-- The solution of `ψ' = a χ`, `χ' = b ψ` with `ψ(0) = ψ0`, `χ(0) = χ0`: first component. -/
def solψ (z : ℝ) : ℝ := ψ0 + J (fun t => a t * linχ a b ψ0 χ0 t) z

/-- The solution of `ψ' = a χ`, `χ' = b ψ` with `ψ(0) = ψ0`, `χ(0) = χ0`: second component. -/
def solχ (z : ℝ) : ℝ := χ0 + J (fun t => b t * linψ a b ψ0 χ0 t) z

variable {a b}

lemma pic_tendsto (ha : Continuous a) (hb : Continuous b) (z : ℝ) :
    Tendsto (fun n => (pic a b ψ0 χ0 n).1 z) atTop (𝓝 (linψ a b ψ0 χ0 z)) ∧
      Tendsto (fun n => (pic a b ψ0 χ0 n).2 z) atTop (𝓝 (linχ a b ψ0 χ0 z)) :=
  ⟨(pic_cauchy ψ0 χ0 ha hb z).1.tendsto_limUnder, (pic_cauchy ψ0 χ0 ha hb z).2.tendsto_limUnder⟩

lemma lin_bounded (ha : Continuous a) (hb : Continuous b) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∀ x : ℝ, max x 0 ≤ R → |linψ a b ψ0 χ0 x| ≤ C ∧ |linχ a b ψ0 χ0 x| ≤ C := by
  obtain ⟨C, hC⟩ := pic_bounded ψ0 χ0 ha hb hR
  exact ⟨C, fun x hx =>
    ⟨le_of_tendsto' (pic_tendsto ψ0 χ0 ha hb x).1.abs fun n => (hC n x hx).1,
      le_of_tendsto' (pic_tendsto ψ0 χ0 ha hb x).2.abs fun n => (hC n x hx).2⟩⟩

lemma lin_measurable (ha : Continuous a) (hb : Continuous b) :
    Measurable (linψ a b ψ0 χ0) ∧ Measurable (linχ a b ψ0 χ0) :=
  ⟨measurable_of_tendsto_metrizable (fun n => (pic_continuous ψ0 χ0 ha hb n).1.measurable)
      (tendsto_pi_nhds.2 fun z => (pic_tendsto ψ0 χ0 ha hb z).1),
    measurable_of_tendsto_metrizable (fun n => (pic_continuous ψ0 χ0 ha hb n).2.measurable)
      (tendsto_pi_nhds.2 fun z => (pic_tendsto ψ0 χ0 ha hb z).2)⟩

/-- A product of a continuous function with a measurable, locally bounded one is interval
integrable; applied to `a · linχ` and `b · linψ`. -/
lemma lin_intervalIntegrable (ha : Continuous a) (hb : Continuous b) (s t : ℝ) :
    IntervalIntegrable (fun x => a x * linχ a b ψ0 χ0 x) volume s t ∧
      IntervalIntegrable (fun x => b x * linψ a b ψ0 χ0 x) volume s t := by
  have hR : 0 ≤ max (max s t) 0 := le_max_right _ _
  obtain ⟨C, hC⟩ := lin_bounded ψ0 χ0 ha hb hR
  obtain ⟨hm1, hm2⟩ := lin_measurable ψ0 χ0 ha hb
  obtain ⟨Ma, hMa⟩ := (isCompact_uIcc (a := s) (b := t)).bddAbove_image
    (f := fun x => |a x| + |b x|) (by fun_prop : Continuous fun x => |a x| + |b x|).continuousOn
  have hx : ∀ x ∈ Set.uIoc s t, max x 0 ≤ max (max s t) 0 ∧ |a x| + |b x| ≤ Ma := fun x hx => by
    have h1 : x ≤ max s t := hx.2
    exact ⟨max_le_max h1 le_rfl, hMa ⟨x, uIoc_subset_uIcc hx, rfl⟩⟩
  constructor
  · refine (intervalIntegrable_const (c := Ma * C)).mono_fun'
      (ha.measurable.mul hm2).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx' => ?_))
    obtain ⟨h1, h2⟩ := hx x hx'
    show ‖a x * linχ a b ψ0 χ0 x‖ ≤ Ma * C
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (by linarith [abs_nonneg (b x)]) (hC x h1).2 (abs_nonneg _)
      ((abs_nonneg _).trans (by linarith [abs_nonneg (b x)] : |a x| ≤ Ma))
  · refine (intervalIntegrable_const (c := Ma * C)).mono_fun'
      (hb.measurable.mul hm1).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx' => ?_))
    obtain ⟨h1, h2⟩ := hx x hx'
    show ‖b x * linψ a b ψ0 χ0 x‖ ≤ Ma * C
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (by linarith [abs_nonneg (a x)]) (hC x h1).1 (abs_nonneg _)
      ((abs_nonneg _).trans (by linarith [abs_nonneg (a x)] : |b x| ≤ Ma))

/-- The limits satisfy the (clamped) integral equations. -/
lemma lin_eq (ha : Continuous a) (hb : Continuous b) (z : ℝ) :
    linψ a b ψ0 χ0 z = solψ a b ψ0 χ0 (max z 0) ∧ linχ a b ψ0 χ0 z = solχ a b ψ0 χ0 (max z 0) := by
  have hR : 0 ≤ max z 0 := le_max_right _ _
  obtain ⟨C, hC⟩ := pic_bounded ψ0 χ0 ha hb hR
  obtain ⟨M, hM⟩ := exists_bound_on (q := fun t => |a t| + |b t|) (by fun_prop) (max z 0)
  have hM0 : 0 ≤ M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hM 0 le_rfl hR)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0 (by simp)).1
  have hcl : ∀ t, 0 ≤ t → t ≤ max z 0 → max t 0 ≤ max z 0 := fun t h0 h1 => by
    rw [max_eq_left h0]
    exact h1
  have t1 := J_tendsto_on (F := fun n t => a t * (pic a b ψ0 χ0 n).2 t)
    (f := fun t => a t * linχ a b ψ0 χ0 t) (C := M * C) hR
    (fun n => ha.mul (pic_continuous ψ0 χ0 ha hb n).2)
    (fun n t h0 h1 => by
      rw [abs_mul]
      exact mul_le_mul (by linarith [hM t h0 h1, abs_nonneg (b t)]) (hC n t (hcl t h0 h1)).2
        (abs_nonneg _) hM0)
    (fun t => (pic_tendsto ψ0 χ0 ha hb t).2.const_mul (a t))
  have t2 := J_tendsto_on (F := fun n t => b t * (pic a b ψ0 χ0 n).1 t)
    (f := fun t => b t * linψ a b ψ0 χ0 t) (C := M * C) hR
    (fun n => hb.mul (pic_continuous ψ0 χ0 ha hb n).1)
    (fun n t h0 h1 => by
      rw [abs_mul]
      exact mul_le_mul (by linarith [hM t h0 h1, abs_nonneg (a t)]) (hC n t (hcl t h0 h1)).1
        (abs_nonneg _) hM0)
    (fun t => (pic_tendsto ψ0 χ0 ha hb t).1.const_mul (b t))
  constructor
  · have h1 : Tendsto (fun n => (pic a b ψ0 χ0 (n + 1)).1 z) atTop (𝓝 (linψ a b ψ0 χ0 z)) :=
      (pic_tendsto ψ0 χ0 ha hb z).1.comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique h1 (t1.const_add ψ0)
  · have h1 : Tendsto (fun n => (pic a b ψ0 χ0 (n + 1)).2 z) atTop (𝓝 (linχ a b ψ0 χ0 z)) :=
      (pic_tendsto ψ0 χ0 ha hb z).2.comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique h1 (t2.const_add χ0)

lemma sol_continuous (ha : Continuous a) (hb : Continuous b) :
    Continuous (solψ a b ψ0 χ0) ∧ Continuous (solχ a b ψ0 χ0) := by
  constructor
  · have := intervalIntegral.continuous_primitive
      (fun s t => (lin_intervalIntegrable ψ0 χ0 ha hb s t).1) 0
    exact continuous_const.add this
  · have := intervalIntegral.continuous_primitive
      (fun s t => (lin_intervalIntegrable ψ0 χ0 ha hb s t).2) 0
    exact continuous_const.add this

lemma lin_continuous (ha : Continuous a) (hb : Continuous b) :
    Continuous (linψ a b ψ0 χ0) ∧ Continuous (linχ a b ψ0 χ0) := by
  obtain ⟨c1, c2⟩ := sol_continuous ψ0 χ0 ha hb
  have e1 : linψ a b ψ0 χ0 = fun z => solψ a b ψ0 χ0 (max z 0) :=
    funext fun z => (lin_eq ψ0 χ0 ha hb z).1
  have e2 : linχ a b ψ0 χ0 = fun z => solχ a b ψ0 χ0 (max z 0) :=
    funext fun z => (lin_eq ψ0 χ0 ha hb z).2
  rw [e1, e2]
  exact ⟨by fun_prop, by fun_prop⟩

lemma lin_eq_sol (ha : Continuous a) (hb : Continuous b) {z : ℝ} (hz : 0 ≤ z) :
    linψ a b ψ0 χ0 z = solψ a b ψ0 χ0 z ∧ linχ a b ψ0 χ0 z = solχ a b ψ0 χ0 z := by
  have := lin_eq ψ0 χ0 ha hb z
  rwa [max_eq_left hz] at this

@[simp] lemma solψ_zero : solψ a b ψ0 χ0 0 = ψ0 := by simp [solψ]

@[simp] lemma solχ_zero : solχ a b ψ0 χ0 0 = χ0 := by simp [solχ]

/-- **Existence**: `(solψ, solχ)` solves the system on every interval `[0, T]`. -/
theorem sol_isLinOn (ha : Continuous a) (hb : Continuous b) (T : ℝ) :
    IsLinOn a b T (solψ a b ψ0 χ0) (solχ a b ψ0 χ0) := by
  obtain ⟨c1, c2⟩ := lin_continuous ψ0 χ0 ha hb
  constructor
  · intro z hz _
    have := (J_hasDerivAt (ha.mul c2) z).const_add ψ0
    rw [(lin_eq_sol ψ0 χ0 ha hb hz).2] at this
    exact this
  · intro z hz _
    have := (J_hasDerivAt (hb.mul c1) z).const_add χ0
    rw [(lin_eq_sol ψ0 χ0 ha hb hz).1] at this
    exact this

lemma sol_nonneg (ha : Continuous a) (hb : Continuous b) (hψ : 0 ≤ ψ0) (hχ : 0 ≤ χ0)
    (ha0 : ∀ z, 0 ≤ a z) (hb0 : ∀ z, 0 ≤ b z) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ solψ a b ψ0 χ0 z ∧ χ0 ≤ solχ a b ψ0 χ0 z := by
  rw [← (lin_eq_sol ψ0 χ0 ha hb hz).1, ← (lin_eq_sol ψ0 χ0 ha hb hz).2]
  exact ⟨ge_of_tendsto' (pic_tendsto ψ0 χ0 ha hb z).1 fun n => (pic_nonneg ψ0 χ0 hψ hχ ha0 hb0 n z).1,
    ge_of_tendsto' (pic_tendsto ψ0 χ0 ha hb z).2 fun n => (pic_nonneg ψ0 χ0 hψ hχ ha0 hb0 n z).2⟩

end Picard

/-- **Positivity** for cooperative systems: if `a, b ≥ 0` and the initial values are
non-negative, then `ψ ≥ 0` and `χ ≥ χ(0)` on `[0, T]`. -/
theorem IsLinOn.nonneg {a b : ℝ → ℝ} {T : ℝ} {ψ χ : ℝ → ℝ} (ha : Continuous a)
    (hb : Continuous b) (ha0 : ∀ z, 0 ≤ a z) (hb0 : ∀ z, 0 ≤ b z) (h : IsLinOn a b T ψ χ)
    (hψ : 0 ≤ ψ 0) (hχ : 0 ≤ χ 0) {z : ℝ} (hz : 0 ≤ z) (hzT : z ≤ T) :
    0 ≤ ψ z ∧ χ 0 ≤ χ z := by
  have hu := h.unique ha hb ha0 hb0 (sol_isLinOn (ψ 0) (χ 0) ha hb T) (by simp) (by simp) hz hzT
  rw [hu.1, hu.2]
  exact sol_nonneg (ψ 0) (χ 0) ha hb hψ hχ ha0 hb0 hz

end Blasius

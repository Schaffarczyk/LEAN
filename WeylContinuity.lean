/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Continuity of Weyl's operator `Φ_λ` (Lemma 5)

Reference: H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
Annals of Mathematics 43 (1942), 381–407, pp. 404–405.

Weyl's topology on functions on `[0, ∞)` is uniform convergence on each finite interval;
`LocUnif U G g` expresses `G i → g` in this sense along a filter `U`.

* `lin_stability`: quantitative continuous dependence of the solutions of
  `ψ' = a χ`, `χ' = b ψ` on the coefficients (energy estimate);
* `PhiL_tendsto_ultrafilter`: **Lemma 5** along an ultrafilter.  As in Weyl's proof, the
  constants `l⁽ⁿ⁾ = -ω⁽ⁿ⁾'(0)` lie in the compact interval `[0, c₁]` (Lemma 1), any limit
  `l*` yields a solution with (40), and the uniqueness part of the auxiliary theorem
  gives `l* = l`;
* `PhiL_tendsto`: Lemma 5 along an arbitrary filter.
-/
import WeylOperator

open Set Filter Topology MeasureTheory

noncomputable section

namespace Blasius

/-! ## Uniform convergence on finite intervals -/

/-- `G i → g` uniformly on each interval `[0, R]`, along the filter `U`. -/
def LocUnif {ι : Type*} (U : Filter ι) (G : ι → ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in U, ∀ t, 0 ≤ t → t ≤ R → |G i t - g t| ≤ ε

lemma tendsto_of_forall_abs_le {ι : Type*} {U : Filter ι} {f : ι → ℝ} {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, |f i - c| ≤ ε) : Tendsto f U (𝓝 c) :=
  Metric.tendsto_nhds.2 fun ε hε => (h (ε / 2) (half_pos hε)).mono fun i hi => by
    rw [Real.dist_eq]
    linarith

lemma J_le_const_on {u : ℝ → ℝ} (hu : Continuous u) {c z : ℝ} (hz : 0 ≤ z)
    (h : ∀ t, 0 ≤ t → t ≤ z → u t ≤ c) : J u z ≤ c * z := by
  have : J u z ≤ J (fun _ => c) z :=
    intervalIntegral.integral_mono_on hz (hu.intervalIntegrable 0 z)
      ((continuous_const : Continuous fun _ : ℝ => c).intervalIntegrable 0 z)
      fun t ht => h t ht.1 ht.2
  rw [← J_const c z]
  exact this

namespace LocUnif

variable {ι : Type*} {U V : Filter ι} {G : ι → ℝ → ℝ} {g : ℝ → ℝ}

lemma mono (h : LocUnif U G g) (hV : V ≤ U) : LocUnif V G g :=
  fun R ε hε => (h R ε hε).filter_mono hV

lemma pointwise (h : LocUnif U G g) {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun i => G i z) U (𝓝 (g z)) :=
  tendsto_of_forall_abs_le fun ε hε => (h z ε hε).mono fun _ hi => hi z hz le_rfl

/-- Primitives converge uniformly on finite intervals. -/
lemma primitive (hG : ∀ i, Continuous (G i)) (hg : Continuous g) (h : LocUnif U G g) :
    LocUnif U (fun i => J (G i)) (J g) := by
  intro R ε hε
  by_cases hR : 0 ≤ R
  · have hR1 : 0 < R + 1 := by linarith
    filter_upwards [h R (ε / (R + 1)) (by positivity)] with i hi t h0 h1
    have := J_sub_le_on (hG i) hg (d := fun _ => ε / (R + 1)) continuous_const (a := R)
      (fun s hs hsR => hi s hs hsR) h0 h1
    rw [J_const] at this
    refine this.trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hR1]
    nlinarith
  · exact Eventually.of_forall fun _ t h0 h1 => absurd (h0.trans h1) hR

end LocUnif

/-! ## Bounds for the coefficients, uniform in `g ∈ 𝔊` -/

lemma abs_exp_sub_le {x y M : ℝ} (hx : x ≤ M) (hy : y ≤ M) :
    |Real.exp x - Real.exp y| ≤ Real.exp M * |x - y| := by
  have h := abs_exp_neg_sub_le (a := M - x) (b := M - y) (by linarith) (by linarith)
  have e1 : Real.exp x = Real.exp M * Real.exp (-(M - x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp y = Real.exp M * Real.exp (-(M - y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e3 : |M - x - (M - y)| = |x - y| := by
    rw [abs_sub_comm x y]
    congr 1
    ring
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos M)]
  rw [e3] at h
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos M).le

namespace InG

variable {g : ℝ → ℝ} (hg : InG g)
include hg

lemma F0_le {R z : ℝ} (hz : 0 ≤ z) (hzR : z ≤ R) : F0 g z ≤ R * R := by
  have h1 := J_le_const_on hg.F1_continuous (c := R) hz
    (fun t h0 h1 => (hg.F1_le h0).trans (h1.trans hzR))
  have : R * z ≤ R * R := mul_le_mul_of_nonneg_left hzR (hz.trans hzR)
  exact h1.trans this

lemma JF0_le {R z : ℝ} (hz : 0 ≤ z) (hzR : z ≤ R) : J (F0 g) z ≤ R ^ 3 := by
  have h1 := J_le_const_on hg.F0_continuous (c := R * R) hz
    (fun t h0 h1 => hg.F0_le h0 (h1.trans hzR))
  have hR := hz.trans hzR
  have : R * R * z ≤ R * R * R := mul_le_mul_of_nonneg_left hzR (by positivity)
  nlinarith

lemma pp_le {R z : ℝ} (hz : 0 ≤ z) (hzR : z ≤ R) : pp g z ≤ Real.exp (2 * R ^ 3) := by
  rw [pp, Real.exp_le_exp]
  linarith [hg.JF0_le hz hzR]

/-- Uniform bound for the coefficients on `[0, R]`. -/
lemma coeff_bound {lam : ℝ} (hlam : 0 ≤ lam) {R x : ℝ} (hx : 0 ≤ x) (hxR : x ≤ R) :
    |aL g x| ≤ Real.exp (2 * R ^ 3) + 4 * lam * R ∧
      |bL lam g x| ≤ Real.exp (2 * R ^ 3) + 4 * lam * R := by
  have hR := hx.trans hxR
  have hp := InG.pp_pos (g := g) x
  have hp1 := hg.one_le_pp hx
  have hE := Real.exp_pos (2 * R ^ 3)
  have h4 : 0 ≤ 4 * lam * R := by positivity
  constructor
  · rw [aL_eq hx, abs_of_pos hp]
    linarith [hg.pp_le hx hxR]
  · rw [bL_eq lam hx]
    have h1 := hg.F1_nonneg hx
    have h2 := (hg.F1_le hx).trans hxR
    rw [abs_of_nonneg (by positivity)]
    have : 4 * lam * F1 g x / pp g x ≤ 4 * lam * F1 g x := div_le_self (by positivity) hp1
    have : 4 * lam * F1 g x ≤ 4 * lam * R := mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith

end InG

section Coefficients

variable {ι : Type*} {U : Filter ι} {G : ι → ℝ → ℝ} {g : ℝ → ℝ}

lemma locUnif_F1 (hG : ∀ i, InG (G i)) (hg : InG g) (h : LocUnif U G g) :
    LocUnif U (fun i => F1 (G i)) (F1 g) :=
  h.primitive (fun i => (hG i).cont) hg.cont

lemma locUnif_pp (hG : ∀ i, InG (G i)) (hg : InG g) (h : LocUnif U G g) :
    LocUnif U (fun i => pp (G i)) (pp g) := by
  have h3 : LocUnif U (fun i => J (F0 (G i))) (J (F0 g)) :=
    ((locUnif_F1 hG hg h).primitive (fun i => (hG i).F1_continuous) hg.F1_continuous).primitive
      (fun i => (hG i).F0_continuous) hg.F0_continuous
  intro R ε hε
  have hE := Real.exp_pos (2 * R ^ 3)
  filter_upwards [h3 R (ε / (2 * Real.exp (2 * R ^ 3))) (by positivity)] with i hi t h0 h1
  have b1 := (hG i).JF0_le h0 h1
  have b2 := hg.JF0_le h0 h1
  have := abs_exp_sub_le (x := 2 * J (F0 (G i)) t) (y := 2 * J (F0 g) t) (M := 2 * R ^ 3)
    (by linarith) (by linarith)
  rw [← mul_sub, abs_mul, abs_two] at this
  have hi' := hi t h0 h1
  show |Real.exp (2 * J (F0 (G i)) t) - Real.exp (2 * J (F0 g) t)| ≤ ε
  refine this.trans ?_
  calc Real.exp (2 * R ^ 3) * (2 * |J (F0 (G i)) t - J (F0 g) t|)
      ≤ Real.exp (2 * R ^ 3) * (2 * (ε / (2 * Real.exp (2 * R ^ 3)))) := by gcongr
    _ = ε := by field_simp

lemma locUnif_aL (hG : ∀ i, InG (G i)) (hg : InG g) (h : LocUnif U G g) :
    LocUnif U (fun i => aL (G i)) (aL g) := by
  intro R ε hε
  filter_upwards [locUnif_pp hG hg h R ε hε] with i hi t h0 h1
  rw [InG.aL_eq h0, InG.aL_eq h0]
  exact hi t h0 h1

lemma locUnif_bL (lam : ℝ) (hlam : 0 ≤ lam) (hG : ∀ i, InG (G i)) (hg : InG g)
    (h : LocUnif U G g) : LocUnif U (fun i => bL lam (G i)) (bL lam g) := by
  intro R ε hε
  by_cases hR : 0 ≤ R
  · set K := 4 * lam * (1 + R) + 1 with hK
    have hK0 : 0 < K := by positivity
    filter_upwards [locUnif_F1 hG hg h R (ε / K) (by positivity),
      locUnif_pp hG hg h R (ε / K) (by positivity)] with i hi1 hi2 t h0 h1
    rw [InG.bL_eq lam h0, InG.bL_eq lam h0]
    have hp := (hG i).one_le_pp h0
    have hp' := hg.one_le_pp h0
    have hpp := InG.pp_pos (g := G i) t
    have hpp' := InG.pp_pos (g := g) t
    have hF := hg.F1_nonneg h0
    have hF' := (hg.F1_le h0).trans h1
    have e : 4 * lam * F1 (G i) t / pp (G i) t - 4 * lam * F1 g t / pp g t
        = 4 * lam * ((F1 (G i) t - F1 g t) / pp (G i) t
          + F1 g t * (pp g t - pp (G i) t) / (pp (G i) t * pp g t)) := by
      field_simp
      ring
    have b1 : |(F1 (G i) t - F1 g t) / pp (G i) t| ≤ ε / K := by
      rw [abs_div, abs_of_pos hpp]
      exact (div_le_self (abs_nonneg _) hp).trans (hi1 t h0 h1)
    have b2 : |F1 g t * (pp g t - pp (G i) t) / (pp (G i) t * pp g t)| ≤ R * (ε / K) := by
      rw [abs_div, abs_mul, abs_of_nonneg hF, abs_of_pos (mul_pos hpp hpp')]
      have h3 : |pp g t - pp (G i) t| ≤ ε / K := by
        rw [abs_sub_comm]
        exact hi2 t h0 h1
      have h4 : (1 : ℝ) ≤ pp (G i) t * pp g t := by nlinarith
      exact (div_le_self (by positivity) h4).trans
        (mul_le_mul hF' h3 (abs_nonneg _) hR)
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * lam)]
    have b3 := (abs_add_le _ _).trans (add_le_add b1 b2)
    calc 4 * lam * |(F1 (G i) t - F1 g t) / pp (G i) t
          + F1 g t * (pp g t - pp (G i) t) / (pp (G i) t * pp g t)|
        ≤ 4 * lam * (ε / K + R * (ε / K)) := mul_le_mul_of_nonneg_left b3 (by positivity)
      _ = (4 * lam * (1 + R)) * ε / K := by ring
      _ ≤ ε := by
          rw [div_le_iff₀ hK0]
          nlinarith
  · exact Eventually.of_forall fun _ t h0 h1 => absurd (h0.trans h1) hR

end Coefficients

/-! ## Continuous dependence of the linear system on its coefficients -/

/-- Energy estimate: two solutions with the same initial values, for coefficients that
differ by at most `δ` on `[0, R]`, differ by `O(δ)`. -/
lemma lin_stability {a b a' b' ψ χ ψ' χ' : ℝ → ℝ} {R M C δ : ℝ}
    (h : IsLinOn a b R ψ χ) (h' : IsLinOn a' b' R ψ' χ') (h0 : ψ' 0 = ψ 0) (h0' : χ' 0 = χ 0)
    (hM0 : 0 ≤ M) (hM : ∀ x, 0 ≤ x → x ≤ R → |a' x| ≤ M ∧ |b' x| ≤ M)
    (hC : ∀ x, 0 ≤ x → x ≤ R → ψ x ^ 2 + χ x ^ 2 ≤ C)
    (hδ : ∀ x, 0 ≤ x → x ≤ R → |a' x - a x| ≤ δ ∧ |b' x - b x| ≤ δ) {z : ℝ} (hz : 0 ≤ z)
    (hzR : z ≤ R) :
    (ψ' z - ψ z) ^ 2 + (χ' z - χ z) ^ 2 ≤ δ ^ 2 * C * Real.exp ((2 * M + 2) * R) := by
  have hR := hz.trans hzR
  have hc0 : 0 < 2 * M + 2 := by positivity
  have hC0 : 0 ≤ C := (by positivity : 0 ≤ ψ 0 ^ 2 + χ 0 ^ 2).trans (hC 0 le_rfl hR)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = δ ^ 2 * C / (2 * M + 2) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hKc : K * (2 * M + 2) = δ ^ 2 * C := by rw [hKdef]; exact div_mul_cancel₀ _ hc0.ne'
  -- derivative of the energy
  have hN : ∀ x, 0 ≤ x → x ≤ R →
      HasDerivAt (fun x => (ψ' x - ψ x) ^ 2 + (χ' x - χ x) ^ 2)
        (2 * (ψ' x - ψ x) * (a' x * χ' x - a x * χ x)
          + 2 * (χ' x - χ x) * (b' x * ψ' x - b x * ψ x)) x := by
    intro x hx0 hxR
    have := (((h'.dψ x hx0 hxR).sub (h.dψ x hx0 hxR)).pow 2).add
      (((h'.dχ x hx0 hxR).sub (h.dχ x hx0 hxR)).pow 2)
    deriv_conv this
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.sub_apply]
  have hN' : ∀ x, 0 ≤ x → x ≤ R →
      2 * (ψ' x - ψ x) * (a' x * χ' x - a x * χ x)
        + 2 * (χ' x - χ x) * (b' x * ψ' x - b x * ψ x)
      ≤ (2 * M + 2) * ((ψ' x - ψ x) ^ 2 + (χ' x - χ x) ^ 2) + δ ^ 2 * C := by
    intro x hx0 hxR
    obtain ⟨hMa, hMb⟩ := hM x hx0 hxR
    obtain ⟨hδa, hδb⟩ := hδ x hx0 hxR
    have hCx := hC x hx0 hxR
    obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ψ' x - ψ x := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e : ℝ, e = χ' x - χ x := ⟨_, rfl⟩
    have hde : |2 * (d * e)| ≤ d ^ 2 + e ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (d + e), sq_nonneg (d - e)]
    have t1 : a' x * (2 * (d * e)) ≤ M * (d ^ 2 + e ^ 2) :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul hMa hde (abs_nonneg _) hM0)
    have t2 : b' x * (2 * (d * e)) ≤ M * (d ^ 2 + e ^ 2) :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul hMb hde (abs_nonneg _) hM0)
    have sa : (a' x - a x) ^ 2 ≤ δ ^ 2 := sq_le_sq' (neg_le_of_abs_le hδa) (le_of_abs_le hδa)
    have sb : (b' x - b x) ^ 2 ≤ δ ^ 2 := sq_le_sq' (neg_le_of_abs_le hδb) (le_of_abs_le hδb)
    have t3 : 2 * d * ((a' x - a x) * χ x) ≤ d ^ 2 + δ ^ 2 * χ x ^ 2 := by
      have := mul_le_mul_of_nonneg_right sa (sq_nonneg (χ x))
      nlinarith [sq_nonneg (d - (a' x - a x) * χ x)]
    have t4 : 2 * e * ((b' x - b x) * ψ x) ≤ e ^ 2 + δ ^ 2 * ψ x ^ 2 := by
      have := mul_le_mul_of_nonneg_right sb (sq_nonneg (ψ x))
      nlinarith [sq_nonneg (e - (b' x - b x) * ψ x)]
    have e1 : a' x * χ' x - a x * χ x = a' x * e + (a' x - a x) * χ x := by
      rw [he]
      ring
    have e2 : b' x * ψ' x - b x * ψ x = b' x * d + (b' x - b x) * ψ x := by
      rw [hd]
      ring
    have hδC : δ ^ 2 * (ψ x ^ 2 + χ x ^ 2) ≤ δ ^ 2 * C :=
      mul_le_mul_of_nonneg_left hCx (sq_nonneg δ)
    have hδC' : δ ^ 2 * χ x ^ 2 + δ ^ 2 * ψ x ^ 2 ≤ δ ^ 2 * C := by
      rw [← mul_add, add_comm]
      exact hδC
    have e3 : 2 * d * (a' x * e + (a' x - a x) * χ x) + 2 * e * (b' x * d + (b' x - b x) * ψ x)
        = a' x * (2 * (d * e)) + b' x * (2 * (d * e)) + 2 * d * ((a' x - a x) * χ x)
          + 2 * e * ((b' x - b x) * ψ x) := by ring
    have e4 : (2 * M + 2) * (d ^ 2 + e ^ 2) = M * (d ^ 2 + e ^ 2) + M * (d ^ 2 + e ^ 2)
        + 2 * d ^ 2 + 2 * e ^ 2 := by ring
    rw [e1, e2, ← hd, ← he, e3, e4]
    linarith [sq_nonneg d, sq_nonneg e]
  -- `(N + K) e^{-c x}` is non-increasing
  have hG : ∀ x, 0 ≤ x → x ≤ R →
      HasDerivAt (fun x => ((ψ' x - ψ x) ^ 2 + (χ' x - χ x) ^ 2 + K)
          * Real.exp (-((2 * M + 2) * x)))
        ((2 * (ψ' x - ψ x) * (a' x * χ' x - a x * χ x)
            + 2 * (χ' x - χ x) * (b' x * ψ' x - b x * ψ x)) * Real.exp (-((2 * M + 2) * x))
          + ((ψ' x - ψ x) ^ 2 + (χ' x - χ x) ^ 2 + K)
            * (Real.exp (-((2 * M + 2) * x)) * -(2 * M + 2))) x := by
    intro x hx0 hxR
    have hE : HasDerivAt (fun x : ℝ => Real.exp (-((2 * M + 2) * x)))
        (Real.exp (-((2 * M + 2) * x)) * -(2 * M + 2)) x := by
      have h1 : HasDerivAt (fun x : ℝ => -((2 * M + 2) * x)) (-(2 * M + 2)) x := by
        have := ((hasDerivAt_id x).const_mul (2 * M + 2)).neg
        deriv_conv this
        simp
      exact h1.exp
    have h2 := ((hN x hx0 hxR).add_const K).mul hE
    deriv_conv h2
    rfl
  have hanti := antitoneOn_Icc_of_hasDerivAt (s := 0) (t := R) hG fun x hx0 hxR => by
    have hE := Real.exp_pos (-((2 * M + 2) * x))
    have h1 := hN' x hx0 hxR
    have e : (2 * (ψ' x - ψ x) * (a' x * χ' x - a x * χ x)
          + 2 * (χ' x - χ x) * (b' x * ψ' x - b x * ψ x)) * Real.exp (-((2 * M + 2) * x))
        + ((ψ' x - ψ x) ^ 2 + (χ' x - χ x) ^ 2 + K)
          * (Real.exp (-((2 * M + 2) * x)) * -(2 * M + 2))
        = Real.exp (-((2 * M + 2) * x))
          * (2 * (ψ' x - ψ x) * (a' x * χ' x - a x * χ x)
            + 2 * (χ' x - χ x) * (b' x * ψ' x - b x * ψ x)
            - (2 * M + 2) * ((ψ' x - ψ x) ^ 2 + (χ' x - χ x) ^ 2) - K * (2 * M + 2)) := by
      ring
    rw [e, hKc]
    exact mul_nonpos_of_nonneg_of_nonpos hE.le (by linarith)
  have hle0 := hanti (left_mem_Icc.2 hR) ⟨hz, hzR⟩ hz
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (ψ' z - ψ z) ^ 2 + (χ' z - χ z) ^ 2 := ⟨_, rfl⟩
  have hle : (N + K) * Real.exp (-((2 * M + 2) * z)) ≤ K := by
    rw [hNdef]
    refine hle0.trans (le_of_eq ?_)
    simp [h0, h0']
  rw [← hNdef]
  have hX := Real.exp_pos ((2 * M + 2) * z)
  have hEX : Real.exp (-((2 * M + 2) * z)) * Real.exp ((2 * M + 2) * z) = 1 := by
    rw [← Real.exp_add]
    simp
  have h1 : N + K ≤ K * Real.exp ((2 * M + 2) * z) := by
    calc N + K = (N + K) * Real.exp (-((2 * M + 2) * z)) * Real.exp ((2 * M + 2) * z) := by
          rw [mul_assoc, hEX, mul_one]
      _ ≤ K * Real.exp ((2 * M + 2) * z) := mul_le_mul_of_nonneg_right hle hX.le
  have h2 : Real.exp ((2 * M + 2) * z) ≤ Real.exp ((2 * M + 2) * R) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left hzR hc0.le
  have h3 : K ≤ δ ^ 2 * C := by rw [hKdef]; exact div_le_self (by positivity) (by linarith)
  have h4 : K * Real.exp ((2 * M + 2) * z) ≤ δ ^ 2 * C * Real.exp ((2 * M + 2) * R) :=
    mul_le_mul h3 h2 hX.le (by positivity)
  linarith

/-- Solutions with fixed initial values depend continuously on the coefficients. -/
lemma sol_tendsto {ι : Type*} {U : Filter ι} {A B : ι → ℝ → ℝ} {a b : ℝ → ℝ}
    (hA : ∀ i, Continuous (A i)) (hB : ∀ i, Continuous (B i)) (ha : Continuous a)
    (hb : Continuous b)
    (hbd : ∀ R : ℝ, ∃ M : ℝ, ∀ i x, 0 ≤ x → x ≤ R → |A i x| ≤ M ∧ |B i x| ≤ M)
    (hAa : LocUnif U A a) (hBb : LocUnif U B b) (ψ0 χ0 : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun i => solψ (A i) (B i) ψ0 χ0 z) U (𝓝 (solψ a b ψ0 χ0 z)) ∧
      Tendsto (fun i => solχ (A i) (B i) ψ0 χ0 z) U (𝓝 (solχ a b ψ0 χ0 z)) := by
  obtain ⟨M, hM⟩ := hbd z
  obtain ⟨c1, c2⟩ := sol_continuous ψ0 χ0 ha hb
  obtain ⟨C, hC⟩ := exists_bound_on
    (q := fun x => solψ a b ψ0 χ0 x ^ 2 + solχ a b ψ0 χ0 x ^ 2) (by fun_prop) z
  have hC0 : 0 ≤ C :=
    (by positivity : 0 ≤ solψ a b ψ0 χ0 0 ^ 2 + solχ a b ψ0 χ0 0 ^ 2).trans (hC 0 le_rfl hz)
  set Bc := C * Real.exp ((2 * |M| + 2) * z) with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  have key : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U,
      |solψ (A i) (B i) ψ0 χ0 z - solψ a b ψ0 χ0 z| ≤ ε ∧
        |solχ (A i) (B i) ψ0 χ0 z - solχ a b ψ0 χ0 z| ≤ ε := by
    intro ε hε
    have hδ : 0 < ε / (Bc + 1) := by positivity
    filter_upwards [hAa z _ hδ, hBb z _ hδ] with i hi1 hi2
    have hst := lin_stability (sol_isLinOn ψ0 χ0 ha hb z) (sol_isLinOn ψ0 χ0 (hA i) (hB i) z)
      (by simp) (by simp) (abs_nonneg M)
      (fun x h0 h1 => ⟨((hM i x h0 h1).1).trans (le_abs_self M),
        ((hM i x h0 h1).2).trans (le_abs_self M)⟩)
      hC (fun x h0 h1 => ⟨hi1 x h0 h1, hi2 x h0 h1⟩) hz le_rfl
    have hsq : (ε / (Bc + 1)) ^ 2 * C * Real.exp ((2 * |M| + 2) * z) ≤ ε ^ 2 := by
      have e : (ε / (Bc + 1)) ^ 2 * C * Real.exp ((2 * |M| + 2) * z)
          = ε ^ 2 * (Bc / (Bc + 1) ^ 2) := by
        rw [hBc]
        field_simp
      rw [e]
      have : Bc / (Bc + 1) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      nlinarith [sq_nonneg ε]
    have hN := hst.trans hsq
    constructor
    · exact abs_le_of_sq_le_sq
        (by nlinarith [sq_nonneg (solχ (A i) (B i) ψ0 χ0 z - solχ a b ψ0 χ0 z)]) hε.le
    · exact abs_le_of_sq_le_sq
        (by nlinarith [sq_nonneg (solψ (A i) (B i) ψ0 χ0 z - solψ a b ψ0 χ0 z)]) hε.le
  exact ⟨tendsto_of_forall_abs_le fun ε hε => (key ε hε).mono fun i hi => hi.1,
    tendsto_of_forall_abs_le fun ε hε => (key ε hε).mono fun i hi => hi.2⟩

/-! ## Lemma 5 -/

section Lemma5

variable {ι : Type*} {G : ι → ℝ → ℝ} {g : ℝ → ℝ} {lam : ℝ}

lemma fundamental_tendsto {U : Filter ι} (hlam : 0 ≤ lam) (hG : ∀ i, InG (G i)) (hg : InG g)
    (h : LocUnif U G g) {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun i => etaψ (aL (G i)) (bL lam (G i)) z) U (𝓝 (etaψ (aL g) (bL lam g) z)) ∧
    Tendsto (fun i => etaχ (aL (G i)) (bL lam (G i)) z) U (𝓝 (etaχ (aL g) (bL lam g) z)) ∧
    Tendsto (fun i => thψ (aL (G i)) (bL lam (G i)) z) U (𝓝 (thψ (aL g) (bL lam g) z)) ∧
    Tendsto (fun i => thχ (aL (G i)) (bL lam (G i)) z) U (𝓝 (thχ (aL g) (bL lam g) z)) := by
  have hbd : ∀ R : ℝ, ∃ M : ℝ, ∀ i x, 0 ≤ x → x ≤ R →
      |aL (G i) x| ≤ M ∧ |bL lam (G i) x| ≤ M := fun R =>
    ⟨_, fun i x h0 h1 => (hG i).coeff_bound hlam h0 h1⟩
  have hA := fun i => ((hG i).coop hlam).ca
  have hB := fun i => ((hG i).coop hlam).cb
  have s1 := sol_tendsto hA hB (hg.coop hlam).ca (hg.coop hlam).cb hbd
    (locUnif_aL hG hg h) (locUnif_bL lam hlam hG hg h) 1 0 hz
  have s2 := sol_tendsto hA hB (hg.coop hlam).ca (hg.coop hlam).cb hbd
    (locUnif_aL hG hg h) (locUnif_bL lam hlam hG hg h) 0 1 hz
  exact ⟨s1.1, s1.2, s2.1, s2.2⟩

/-- The constants `l = -ω'(0)` depend continuously on `g` (along an ultrafilter). -/
lemma lw_tendsto_ultrafilter (U : Ultrafilter ι) (hlam : 0 ≤ lam) (hG : ∀ i, InG (G i))
    (hg : InG g) (h : LocUnif (U : Filter ι) G g) :
    Tendsto (fun i => lw (aL (G i)) (bL lam (G i))) U (𝓝 (lw (aL g) (bL lam g))) := by
  -- the values lie in the compact interval `[0, c₁]`
  have hmem : ∀ i, lw (aL (G i)) (bL lam (G i)) ∈ Icc (0 : ℝ) (c1 lam) := fun i =>
    ⟨((hG i).coop hlam).lw_nonneg, (hG i).lw_le hlam⟩
  obtain ⟨ls, -, hls⟩ := isCompact_Icc.ultrafilter_le_nhds
    (U.map fun i => lw (aL (G i)) (bL lam (G i)))
    (by
      rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
      exact univ_mem' hmem)
  have hl : Tendsto (fun i => lw (aL (G i)) (bL lam (G i))) U (𝓝 ls) := hls
  -- the limit satisfies (40), hence equals `l` by uniqueness
  have huniq : ls = lw (aL g) (bL lam g) := by
    refine (hg.coop hlam).lw_unique (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨t1, -, t3, -⟩ := fundamental_tendsto hlam hG hg h hz
      exact ge_of_tendsto' (t1.sub (hl.mul t3)) fun i => (((hG i).coop hlam).om_sign hz).1
    · obtain ⟨-, t2, -, t4⟩ := fundamental_tendsto hlam hG hg h hz
      exact le_of_tendsto' (t2.sub (hl.mul t4)) fun i => (((hG i).coop hlam).om_sign hz).2
  rw [← huniq]
  exact hl

/-- **Weyl's Lemma 5** along an ultrafilter: `Φ_λ{g}` depends continuously on `g ∈ 𝔊`. -/
theorem PhiL_tendsto_ultrafilter (U : Ultrafilter ι) (hlam : 0 ≤ lam) (hG : ∀ i, InG (G i))
    (hg : InG g) (h : LocUnif (U : Filter ι) G g) (z : ℝ) :
    Tendsto (fun i => PhiL lam (G i) z) U (𝓝 (PhiL lam g z)) := by
  have hz : 0 ≤ max z 0 := le_max_right _ _
  obtain ⟨t1, -, t3, -⟩ := fundamental_tendsto hlam hG hg h hz
  have tl := lw_tendsto_ultrafilter U hlam hG hg h
  have tp := (locUnif_pp hG hg h).pointwise hz
  exact (t1.sub (tl.mul t3)).div tp (InG.pp_pos _).ne'

/-- **Weyl's Lemma 5** along an arbitrary filter. -/
theorem PhiL_tendsto {U : Filter ι} (hlam : 0 ≤ lam) (hG : ∀ i, InG (G i)) (hg : InG g)
    (h : LocUnif U G g) (z : ℝ) :
    Tendsto (fun i => PhiL lam (G i) z) U (𝓝 (PhiL lam g z)) :=
  (tendsto_iff_ultrafilter _ _ _).2 fun V hV =>
    PhiL_tendsto_ultrafilter V hlam hG hg (h.mono hV) z

end Lemma5

end Blasius

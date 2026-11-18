/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Weyl's fixed-point principle (§7 and Appendix)

Reference: H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
Annals of Mathematics 43 (1942), 381–407, pp. 404 and 406–407.

Weyl's "general principle": an operator that is continuous on `𝔊` and maps `𝔊` into an
equicontinuous subset has a fixed point.  We follow the constructive argument of the
Appendix, specialised to `Φ_λ`:

1. `pl`: piecewise linear interpolation with nodes `m / n`, constant beyond the last node;
2. `approx_fixed`: Brouwer's theorem on the cube `[0,1]^(N+1)`, applied to
   `x ↦ (Φ_λ{g_x}(m/n))_m`, gives `γ ∈ 𝔊` with `|Φ_λ{γ} - γ| ≤ 2 (c₁ + c₂ ν²) / n` on `[0, ν]`
   (Weyl's (54));
3. `exists_fixed_of_brouwer`: a limit of such approximate fixed points is a fixed point.
   Instead of Weyl's subsequence we take pointwise limits along an ultrafilter;
   equicontinuity (Lemma 2) upgrades them to uniform convergence on finite intervals, and
   Lemma 5 gives `Φ_λ{g} = g`.

Brouwer's theorem enters as the hypothesis `BrouwerCube`; it is discharged in
`WeylMain.lean` from an existing formalisation.
-/
import WeylFixed

open Set Filter Topology MeasureTheory

noncomputable section

namespace Blasius

/-- Brouwer's fixed-point theorem for the cubes `[0,1]^(N+1)`. -/
def BrouwerCube : Prop :=
  ∀ (N : ℕ) (T : (Fin (N + 1) → ℝ) → (Fin (N + 1) → ℝ)), Continuous T →
    (∀ x, T x ∈ Icc (0 : Fin (N + 1) → ℝ) 1) → ∃ x ∈ Icc (0 : Fin (N + 1) → ℝ) 1, T x = x

/-! ## Piecewise linear interpolation -/

/-- The ramp `u ↦ min 1 (max 0 u)`. -/
def ramp (u : ℝ) : ℝ := min 1 (max 0 u)

lemma ramp_continuous : Continuous ramp := continuous_const.min (continuous_const.max continuous_id)

lemma ramp_nonneg (u : ℝ) : 0 ≤ ramp u := le_min zero_le_one (le_max_left 0 u)

lemma ramp_le_one (u : ℝ) : ramp u ≤ 1 := min_le_left _ _

lemma ramp_of_nonpos {u : ℝ} (hu : u ≤ 0) : ramp u = 0 := by
  rw [ramp, max_eq_left hu, min_eq_right zero_le_one]

lemma ramp_of_one_le {u : ℝ} (hu : 1 ≤ u) : ramp u = 1 := by
  rw [ramp, max_eq_right (zero_le_one.trans hu), min_eq_left hu]

/-- `pl n x m` is the piecewise linear function with values `x k` at the nodes `k / n`,
`k ≤ m`, constant `x 0` on `(-∞, 0]` and constant `x m` on `[m / n, ∞)`. -/
def pl (n : ℝ) (x : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => x 0
  | m + 1 => fun z => pl n x m z + (x (m + 1) - x m) * ramp (n * z - m)

section PL

variable {n : ℝ} {x y : ℕ → ℝ}

lemma pl_succ (m : ℕ) (z : ℝ) :
    pl n x (m + 1) z = pl n x m z + (x (m + 1) - x m) * ramp (n * z - m) := rfl

lemma pl_continuous : ∀ m, Continuous (pl n x m)
  | 0 => continuous_const
  | m + 1 => by
      have h := pl_continuous m
      have hr : Continuous fun z : ℝ => ramp (n * z - m) :=
        ramp_continuous.comp ((continuous_const.mul continuous_id).sub continuous_const)
      exact h.add (continuous_const.mul hr)

lemma pl_node : ∀ (m : ℕ) (z : ℝ), (m : ℝ) ≤ n * z → pl n x m z = x m
  | 0, _, _ => rfl
  | m + 1, z, h => by
      push_cast at h
      rw [pl_succ, pl_node m z (by linarith), ramp_of_one_le (by linarith)]
      ring

lemma pl_stable_step (m : ℕ) {z : ℝ} (h : n * z ≤ m) : pl n x (m + 1) z = pl n x m z := by
  rw [pl_succ, ramp_of_nonpos (by linarith)]
  ring

lemma pl_stable {m m' : ℕ} (hmm : m ≤ m') {z : ℝ} (h : n * z ≤ m) :
    pl n x m' z = pl n x m z := by
  induction m', hmm using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [pl_stable_step k (h.trans (by exact_mod_cast hk)), ih]

lemma pl_mem (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1) : ∀ (m : ℕ) (z : ℝ), 0 ≤ pl n x m z ∧ pl n x m z ≤ 1
  | 0, _ => hx 0
  | m + 1, z => by
      rcases le_total (n * z) m with h | h
      · rw [pl_stable_step m h]
        exact pl_mem hx m z
      · rw [pl_succ, pl_node m z h]
        have r0 := ramp_nonneg (n * z - m)
        have r1 := ramp_le_one (n * z - m)
        obtain ⟨a0, a1⟩ := hx m
        obtain ⟨b0, b1⟩ := hx (m + 1)
        constructor <;> nlinarith

lemma pl_close {δ : ℝ} (h : ∀ k, |y k - x k| ≤ δ) :
    ∀ (m : ℕ) (z : ℝ), |pl n y m z - pl n x m z| ≤ δ
  | 0, _ => h 0
  | m + 1, z => by
      rcases le_total (n * z) m with hz | hz
      · rw [pl_stable_step m hz, pl_stable_step m hz]
        exact pl_close h m z
      · rw [pl_succ, pl_succ, pl_node m z hz, pl_node m z hz]
        have r0 := ramp_nonneg (n * z - m)
        have r1 := ramp_le_one (n * z - m)
        obtain ⟨a0, a1⟩ := abs_le.1 (h m)
        obtain ⟨b0, b1⟩ := abs_le.1 (h (m + 1))
        rw [abs_le]
        constructor <;> nlinarith

lemma pl_near {k N : ℕ} (hkN : k + 1 ≤ N) {z : ℝ} (h1 : (k : ℝ) ≤ n * z) (h2 : n * z ≤ k + 1) :
    |pl n x N z - x k| ≤ |x (k + 1) - x k| := by
  rw [pl_stable hkN (by push_cast; linarith), pl_succ, pl_node k z h1]
  have r0 := ramp_nonneg (n * z - k)
  have r1 := ramp_le_one (n * z - k)
  have e : x k + (x (k + 1) - x k) * ramp (n * z - k) - x k
      = (x (k + 1) - x k) * ramp (n * z - k) := by ring
  rw [e, abs_mul, abs_of_nonneg r0]
  exact mul_le_of_le_one_right (abs_nonneg _) r1

end PL

/-! ## Approximate fixed points from Brouwer's theorem -/

/-- Clamp to `[0, 1]`. -/
def cl01 (u : ℝ) : ℝ := max 0 (min 1 u)

lemma cl01_mem (u : ℝ) : 0 ≤ cl01 u ∧ cl01 u ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma cl01_of_mem {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : cl01 u = u := by
  rw [cl01, min_eq_right h1, max_eq_right h0]

lemma cl01_sub_le (u v : ℝ) : |cl01 u - cl01 v| ≤ |u - v| := by
  have h1 : |cl01 u - cl01 v| ≤ max |(0 : ℝ) - 0| |min 1 u - min 1 v| :=
    abs_max_sub_max_le_max (0 : ℝ) (min 1 u) 0 (min 1 v)
  have h2 : |min 1 u - min 1 v| ≤ max |(1 : ℝ) - 1| |u - v| :=
    abs_min_sub_min_le_max (1 : ℝ) u 1 v
  have e1 : max |(0 : ℝ) - 0| |min 1 u - min 1 v| = |min 1 u - min 1 v| := by simp
  have e2 : max |(1 : ℝ) - 1| |u - v| = |u - v| := by simp
  rw [e1] at h1
  rw [e2] at h2
  exact h1.trans h2

/-- Extension of a finite vector to a sequence, clamped to `[0, 1]`. -/
def ext01 {N : ℕ} (x : Fin (N + 1) → ℝ) (k : ℕ) : ℝ :=
  cl01 (x ⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩)

lemma ext01_mem {N : ℕ} (x : Fin (N + 1) → ℝ) (k : ℕ) : 0 ≤ ext01 x k ∧ ext01 x k ≤ 1 :=
  cl01_mem _

lemma ext01_close {N : ℕ} (x y : Fin (N + 1) → ℝ) (k : ℕ) :
    |ext01 y k - ext01 x k| ≤ dist y x := by
  refine (cl01_sub_le _ _).trans ?_
  rw [← Real.dist_eq]
  exact dist_le_pi_dist y x _

lemma ext01_eq {N : ℕ} {x : Fin (N + 1) → ℝ} (hx : x ∈ Icc (0 : Fin (N + 1) → ℝ) 1)
    (j : Fin (N + 1)) : ext01 x j = x j := by
  have e : (⟨min (j : ℕ) N, Nat.lt_succ_of_le (min_le_right _ N)⟩ : Fin (N + 1)) = j :=
    Fin.ext (min_eq_left (Nat.lt_succ_iff.1 j.2))
  rw [ext01, e]
  exact cl01_of_mem (hx.1 j) (hx.2 j)

lemma pl_inG {n : ℝ} {x : ℕ → ℝ} (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1) (N : ℕ) : InG (pl n x N) where
  cont := pl_continuous N
  nonneg := fun t _ => (pl_mem hx N t).1
  le_one := fun t _ => (pl_mem hx N t).2

lemma PhiL_mem {lam : ℝ} (hlam : 0 ≤ lam) {g : ℝ → ℝ} (hg : InG g) (z : ℝ) :
    0 ≤ PhiL lam g z ∧ PhiL lam g z ≤ 1 :=
  hg.omg_mem hlam (le_max_right z 0)

lemma PhiL_clamp (lam : ℝ) (g : ℝ → ℝ) (z : ℝ) : PhiL lam g (max z 0) = PhiL lam g z := by
  rw [PhiL, PhiL, max_eq_left (le_max_right z 0)]

/-- **Approximate fixed points** (Weyl's (54)). -/
theorem approx_fixed (hB : BrouwerCube) {lam : ℝ} (hlam : 0 ≤ lam) {n ν : ℕ} (hn : 0 < n)
    (hν : 0 < ν) :
    ∃ γ : ℝ → ℝ, InG γ ∧ ∀ z : ℝ, 0 ≤ z → z ≤ ν →
      |PhiL lam γ z - γ z| ≤ 2 * (c1 lam + c2 lam * (ν : ℝ) ^ 2) / n := by
  set N := n * ν with hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNpos : 0 < N := Nat.mul_pos hn hν
  have hNR : (N : ℝ) = n * ν := by
    rw [hN]
    push_cast
    ring
  -- the map of the cube
  have hG : ∀ x : Fin (N + 1) → ℝ, InG (pl n (ext01 x) N) := fun x => pl_inG (ext01_mem x) N
  have hT : Continuous fun (x : Fin (N + 1) → ℝ) (j : Fin (N + 1)) =>
      PhiL lam (pl n (ext01 x) N) ((j : ℝ) / n) := by
    refine continuous_pi fun j => continuous_iff_continuousAt.2 fun x0 => ?_
    refine PhiL_tendsto hlam hG (hG x0) (fun R ε hε => ?_) _
    filter_upwards [Metric.closedBall_mem_nhds x0 hε] with x hx t _ _
    exact pl_close (fun k => (ext01_close x0 x k).trans (Metric.mem_closedBall.1 hx)) N t
  obtain ⟨x, hx, hfix⟩ := hB N _ hT
    (fun x => ⟨fun j => (PhiL_mem hlam (hG x) _).1, fun j => (PhiL_mem hlam (hG x) _).2⟩)
  refine ⟨pl n (ext01 x) N, hG x, fun z hz0 hzν => ?_⟩
  set γ := pl n (ext01 x) N with hγ
  set L := c1 lam + c2 lam * (ν : ℝ) ^ 2 with hL
  have hc2 : 0 ≤ c2 lam := le_max_right _ _
  have hL0 : 0 ≤ L := by
    have : 0 ≤ c1 lam := by
      unfold c1
      positivity
    positivity
  -- values at the nodes
  have hnode : ∀ k : ℕ, k ≤ N → PhiL lam γ ((k : ℝ) / n) = ext01 x k ∧ γ ((k : ℝ) / n) = ext01 x k := by
    intro k hk
    have e1 : n * ((k : ℝ) / n) = k := by field_simp
    constructor
    · have := congrFun hfix ⟨k, Nat.lt_succ_of_le hk⟩
      simp only at this
      rw [this]
      exact (ext01_eq hx ⟨k, Nat.lt_succ_of_le hk⟩).symm
    · rw [hγ, pl_stable hk (le_of_eq e1)]
      exact pl_node k _ (le_of_eq e1.symm)
  -- the node interval containing `z`
  set k := min ⌊(n : ℝ) * z⌋₊ (N - 1) with hk
  have hnz : 0 ≤ (n : ℝ) * z := by positivity
  have hk1 : k + 1 ≤ N := by
    have : k ≤ N - 1 := min_le_right _ _
    omega
  have hkz : (k : ℝ) ≤ n * z :=
    le_trans (by exact_mod_cast min_le_left _ _) (Nat.floor_le hnz)
  have hzk : (n : ℝ) * z ≤ k + 1 := by
    rcases le_total ⌊(n : ℝ) * z⌋₊ (N - 1) with h | h
    · rw [hk, min_eq_left h]
      exact (Nat.lt_floor_add_one _).le
    · rw [hk, min_eq_right h]
      have : ((N - 1 : ℕ) : ℝ) + 1 = N := by
        have : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
        exact_mod_cast this
      rw [this, hNR]
      exact mul_le_mul_of_nonneg_left hzν hnR.le
  -- the nodes lie in `[0, ν]`
  have hkν : ((k : ℝ) + 1) / n ≤ ν := by
    rw [div_le_iff₀ hnR]
    have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk1
    push_cast at this
    rw [hNR] at this
    linarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
  have hkk : (k : ℝ) / n ≤ ((k : ℝ) + 1) / n := by
    apply div_le_div_of_nonneg_right _ hnR.le
    linarith
  obtain ⟨n1, n2⟩ := hnode k (by omega)
  obtain ⟨n3, -⟩ := hnode (k + 1) hk1
  -- three estimates
  have hzl : (k : ℝ) / n ≤ z := by
    rw [div_le_iff₀ hnR]
    linarith
  have hzr : z ≤ ((k : ℝ) + 1) / n := by
    rw [le_div_iff₀ hnR]
    linarith
  have d1 : |z - (k : ℝ) / n| ≤ 1 / n := by
    rw [abs_of_nonneg (by linarith)]
    have : ((k : ℝ) + 1) / n = (k : ℝ) / n + 1 / n := by ring
    linarith
  have d2 : |((k : ℝ) + 1) / n - (k : ℝ) / n| ≤ 1 / n := by
    have : ((k : ℝ) + 1) / n - (k : ℝ) / n = 1 / n := by ring
    rw [this, abs_of_nonneg (by positivity)]
  have e1 := (hG x).PhiL_lipschitz hlam (R := ν) hz0 hzν hk0 (hkk.trans hkν)
  have e2 := (hG x).PhiL_lipschitz hlam (R := ν) (hk0.trans hkk) hkν hk0 (hkk.trans hkν)
  have e3 := pl_near (n := n) (x := ext01 x) hk1 hkz hzk
  rw [← hγ] at e1 e2 e3
  push_cast at n3
  rw [n3, n1] at e2
  rw [n1] at e1
  have b1 : |PhiL lam γ z - ext01 x k| ≤ L * (1 / n) :=
    e1.trans (mul_le_mul_of_nonneg_left d1 hL0)
  have b2 : |γ z - ext01 x k| ≤ L * (1 / n) :=
    e3.trans (e2.trans (mul_le_mul_of_nonneg_left d2 hL0))
  have b3 : |PhiL lam γ z - γ z| ≤ |PhiL lam γ z - ext01 x k| + |γ z - ext01 x k| := by
    have := abs_sub_le (PhiL lam γ z) (ext01 x k) (γ z)
    rwa [abs_sub_comm (ext01 x k) (γ z)] at this
  have e4 : 2 * L / n = L * (1 / n) + L * (1 / n) := by ring
  rw [e4]
  linarith

/-! ## Passage to the limit -/

section Limit

variable {lam : ℝ} (hlam : 0 ≤ lam) (U : Ultrafilter ℕ) {γ : ℕ → ℝ → ℝ} (hγ : ∀ k, InG (γ k))
include hlam hγ

/-- Pointwise limits along the ultrafilter exist, by compactness of `[0, 1]`. -/
lemma exists_lim (z : ℝ) : ∃ y, Tendsto (fun k => PhiL lam (γ k) z) U (𝓝 y) := by
  obtain ⟨y, -, hy⟩ := isCompact_Icc.ultrafilter_le_nhds
    (U.map fun k => PhiL lam (γ k) z)
    (by
      rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
      exact univ_mem' fun k => ⟨(PhiL_mem hlam (hγ k) z).1, (PhiL_mem hlam (hγ k) z).2⟩)
  exact ⟨y, hy⟩

/-- The pointwise limit of `Φ_λ{γ_k}` along the ultrafilter. -/
def glim (lam : ℝ) (U : Ultrafilter ℕ) (γ : ℕ → ℝ → ℝ) (z : ℝ) : ℝ :=
  limUnder (U : Filter ℕ) (fun k => PhiL lam (γ k) z)

lemma glim_tendsto (z : ℝ) : Tendsto (fun k => PhiL lam (γ k) z) U (𝓝 (glim lam U γ z)) :=
  tendsto_nhds_limUnder (exists_lim hlam U hγ z)

lemma glim_mem (z : ℝ) : 0 ≤ glim lam U γ z ∧ glim lam U γ z ≤ 1 :=
  ⟨ge_of_tendsto' (glim_tendsto hlam U hγ z) fun k => (PhiL_mem hlam (hγ k) z).1,
    le_of_tendsto' (glim_tendsto hlam U hγ z) fun k => (PhiL_mem hlam (hγ k) z).2⟩

lemma glim_clamp (z : ℝ) : glim lam U γ (max z 0) = glim lam U γ z := by
  refine tendsto_nhds_unique (glim_tendsto hlam U hγ (max z 0)) ?_
  refine (glim_tendsto hlam U hγ z).congr fun k => ?_
  exact (PhiL_clamp lam (γ k) z).symm

lemma glim_lipschitz {R x y : ℝ} (hx : 0 ≤ x) (hxR : x ≤ R) (hy : 0 ≤ y) (hyR : y ≤ R) :
    |glim lam U γ x - glim lam U γ y| ≤ (c1 lam + c2 lam * R ^ 2) * |x - y| :=
  le_of_tendsto' ((glim_tendsto hlam U hγ x).sub (glim_tendsto hlam U hγ y)).abs fun k =>
    (hγ k).PhiL_lipschitz hlam hx hxR hy hyR

omit hγ in
lemma c1c2_nonneg (R : ℝ) : 0 ≤ c1 lam + c2 lam * R ^ 2 := by
  have hc2 : 0 ≤ c2 lam := le_max_right _ _
  have : 0 ≤ c1 lam := by
    unfold c1
    positivity
  positivity

lemma glim_inG : InG (glim lam U γ) where
  cont := by
    have hc : ContinuousOn (glim lam U γ) (Ici 0) := by
      intro z0 hz0
      have hz0' : (0 : ℝ) ≤ z0 := hz0
      refine tendsto_of_forall_abs_le fun ε hε => ?_
      set L := c1 lam + c2 lam * (z0 + 1) ^ 2 with hL
      have hL0 : 0 ≤ L := c1c2_nonneg hlam (z0 + 1)
      have hδ : 0 < min 1 (ε / (L + 1)) := lt_min one_pos (by positivity)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds z0 hδ)] with z hz hball
      have hd : |z - z0| ≤ min 1 (ε / (L + 1)) := by
        rw [← Real.dist_eq]
        exact Metric.mem_closedBall.1 hball
      have hd1 : |z - z0| ≤ 1 := hd.trans (min_le_left _ _)
      have hd2 : |z - z0| ≤ ε / (L + 1) := hd.trans (min_le_right _ _)
      have hzle : z ≤ z0 + 1 := by linarith [(abs_le.1 hd1).2]
      have h1 := glim_lipschitz hlam U hγ (R := z0 + 1) (mem_Ici.1 hz) hzle hz0' (by linarith)
      refine h1.trans ?_
      calc L * |z - z0| ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left hd2 hL0
        _ ≤ ε := by
            rw [mul_div_assoc', div_le_iff₀ (by positivity)]
            nlinarith
    have e : glim lam U γ = clamp (glim lam U γ) :=
      funext fun z => (glim_clamp hlam U hγ z).symm
    rw [e]
    exact continuous_clamp hc
  nonneg := fun t _ => (glim_mem hlam U hγ t).1
  le_one := fun t _ => (glim_mem hlam U hγ t).2

/-- Equicontinuity upgrades pointwise convergence to uniform convergence on `[0, R]`. -/
lemma glim_locUnif : LocUnif (U : Filter ℕ) (fun k => PhiL lam (γ k)) (glim lam U γ) := by
  intro R ε hε
  rcases lt_trichotomy R 0 with hR | hR | hR
  · exact Eventually.of_forall fun _ t h0 h1 => absurd (h0.trans h1) (not_le.2 hR)
  · -- `R = 0`: only the point `0`
    have h0 := Metric.tendsto_nhds.1 (glim_tendsto hlam U hγ 0) ε hε
    filter_upwards [h0] with k hk t ht0 ht1
    have : t = 0 := le_antisymm (ht1.trans hR.le) ht0
    rw [this, ← Real.dist_eq]
    exact hk.le
  · set L := c1 lam + c2 lam * R ^ 2 with hL
    have hL0 : 0 ≤ L := c1c2_nonneg hlam R
    -- mesh `d = R / M` with `L d ≤ ε / 3`
    set M := ⌈3 * L * R / ε⌉₊ + 1 with hM
    have hMpos : (0 : ℝ) < M := by
      rw [hM]
      push_cast
      positivity
    have hMge : 3 * L * R / ε ≤ M := by
      rw [hM]
      push_cast
      linarith [Nat.le_ceil (3 * L * R / ε)]
    set d := R / M with hd
    have hd0 : 0 < d := by positivity
    have hLd : L * d ≤ ε / 3 := by
      rw [hd, mul_div_assoc', div_le_iff₀ hMpos]
      rw [div_le_iff₀ hε] at hMge
      nlinarith
    have hev : ∀ᶠ k in (U : Filter ℕ), ∀ j : Fin (M + 1),
        |PhiL lam (γ k) ((j : ℕ) * d) - glim lam U γ ((j : ℕ) * d)| ≤ ε / 3 := by
      rw [eventually_all]
      intro j
      have := Metric.tendsto_nhds.1 (glim_tendsto hlam U hγ ((j : ℕ) * d)) (ε / 3) (by positivity)
      exact this.mono fun k hk => by
        rw [← Real.dist_eq]
        exact hk.le
    filter_upwards [hev] with k hk t ht0 ht1
    -- the mesh point below `t`
    set j := ⌊t / d⌋₊ with hj
    have htd : 0 ≤ t / d := by positivity
    have hjM : j ≤ M := by
      apply Nat.floor_le_of_le
      rw [div_le_iff₀ hd0, hd]
      have : (M : ℝ) * (R / M) = R := by field_simp
      rw [this]
      exact ht1
    have hj1 : (j : ℝ) * d ≤ t := by
      have := Nat.floor_le htd
      rw [le_div_iff₀ hd0] at this
      exact this
    have hj2 : t ≤ (j : ℝ) * d + d := by
      have := (Nat.lt_floor_add_one (t / d)).le
      rw [div_le_iff₀ hd0] at this
      linarith
    have hjR : (j : ℝ) * d ≤ R := hj1.trans ht1
    have hj0 : (0 : ℝ) ≤ (j : ℝ) * d := by positivity
    have habs : |t - (j : ℝ) * d| ≤ d := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have a1 := (hγ k).PhiL_lipschitz hlam (R := R) ht0 ht1 hj0 hjR
    have a2 := hk ⟨j, Nat.lt_succ_of_le hjM⟩
    have a3 := glim_lipschitz hlam U hγ (R := R) hj0 hjR ht0 ht1
    rw [abs_sub_comm ((j : ℝ) * d) t] at a3
    simp only at a2
    have b1 : (c1 lam + c2 lam * R ^ 2) * |t - (j : ℝ) * d| ≤ ε / 3 :=
      (mul_le_mul_of_nonneg_left habs hL0).trans hLd
    have t1 := abs_sub_le (PhiL lam (γ k) t) (PhiL lam (γ k) ((j : ℝ) * d)) (glim lam U γ t)
    have t2 := abs_sub_le (PhiL lam (γ k) ((j : ℝ) * d)) (glim lam U γ ((j : ℝ) * d))
      (glim lam U γ t)
    linarith

end Limit

/-- **Existence of a fixed point of `Φ_λ`**, assuming Brouwer's theorem for cubes. -/
theorem exists_fixed_of_brouwer (hB : BrouwerCube) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ g : ℝ → ℝ, InG g ∧ ∀ z, PhiL lam g z = g z := by
  -- approximate fixed points with error `1 / (k + 1)` on `[0, k + 1]`
  have hstep : ∀ k : ℕ, ∃ γ : ℝ → ℝ, InG γ ∧ ∀ z, 0 ≤ z → z ≤ (k : ℝ) + 1 →
      |PhiL lam γ z - γ z| ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    set L := c1 lam + c2 lam * ((k : ℝ) + 1) ^ 2 with hL
    have hL0 : 0 ≤ L := by
      have hc2 : 0 ≤ c2 lam := le_max_right _ _
      have : 0 ≤ c1 lam := by
        unfold c1
        positivity
      positivity
    obtain ⟨γ, hγ, hγ'⟩ := approx_fixed hB hlam
      (n := ⌈2 * ((k : ℝ) + 1) * L⌉₊ + 1) (ν := k + 1) (Nat.succ_pos _) (Nat.succ_pos _)
    refine ⟨γ, hγ, fun z h0 h1 => ?_⟩
    have h2 := hγ' z h0 (by push_cast; exact h1)
    push_cast at h2
    refine h2.trans ?_
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hn : 2 * ((k : ℝ) + 1) * L ≤ ⌈2 * ((k : ℝ) + 1) * L⌉₊ := Nat.le_ceil _
    rw [div_le_div_iff₀ (by positivity) hk]
    nlinarith
  choose γ hγ hγ' using hstep
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hgl := glim_inG hlam U hγ
  refine ⟨glim lam U γ, hgl, fun z => ?_⟩
  -- `γ_k → glim` uniformly on finite intervals
  have hloc : LocUnif (U : Filter ℕ) γ (glim lam U γ) := by
    intro R ε hε
    have hev : ∀ᶠ k : ℕ in atTop, R ≤ (k : ℝ) + 1 ∧ 1 / ((k : ℝ) + 1) ≤ ε / 2 := by
      filter_upwards [eventually_ge_atTop ⌈max R (2 / ε)⌉₊] with k hk
      have h1 : max R (2 / ε) ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
      have h2 : R ≤ (k : ℝ) := (le_max_left _ _).trans h1
      have h3 : 2 / ε ≤ (k : ℝ) := (le_max_right _ _).trans h1
      refine ⟨by linarith, ?_⟩
      have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      rw [div_le_div_iff₀ hk0 two_pos]
      rw [div_le_iff₀ hε] at h3
      nlinarith
    filter_upwards [hU hev, glim_locUnif hlam U hγ R (ε / 2) (by positivity)] with k hk1 hk2 t h0 h1
    have a1 := hγ' k t h0 (h1.trans hk1.1)
    have a2 := hk2 t h0 h1
    have t1 := abs_sub_le (γ k t) (PhiL lam (γ k) t) (glim lam U γ t)
    rw [abs_sub_comm (γ k t) (PhiL lam (γ k) t)] at t1
    linarith [hk1.2]
  exact tendsto_nhds_unique (PhiL_tendsto_ultrafilter U hlam hγ hgl hloc z)
    (glim_tendsto hlam U hγ z)

end Blasius

namespace Blasius

/-- **Weyl's theorem for problem `(A_λ)`** (p. 406), assuming Brouwer's theorem for cubes:
for `λ ≥ 0` and `k > 0` there is `w` with

  `w''' + 2 w w'' + 2 λ (k² - w'²) = 0` on `[0, ∞)`,  `w(0) = w'(0) = 0`,  `w'(z) → k`.

Here `w₁ = w'`, `w₂ = w''`; the third derivative is one-sided at `0`. -/
theorem weyl_Alam_exists_of_brouwer (hB : BrouwerCube) {lam : ℝ} (hlam : 0 ≤ lam) (k : ℝ)
    (hk : 0 < k) :
    ∃ w w₁ w₂ : ℝ → ℝ,
      (∀ z, HasDerivAt w (w₁ z) z) ∧
      (∀ z, HasDerivAt w₁ (w₂ z) z) ∧
      (∀ z, 0 ≤ z → HasDerivWithinAt w₂
        (-(2 * w z * w₂ z) - 2 * lam * (k ^ 2 - w₁ z ^ 2)) (Ici 0) z) ∧
      w 0 = 0 ∧ w₁ 0 = 0 ∧ Tendsto w₁ atTop (𝓝 k) := by
  rcases hlam.eq_or_lt with h0 | hpos
  · -- `λ = 0`: Blasius's problem, §2
    obtain ⟨w, w₁, w₂, d0, d1, d2, z0, z1, hl⟩ := weyl_A0_exists k hk
    refine ⟨w, w₁, w₂, d0, d1, fun z hz => ?_, z0, z1, hl⟩
    have := d2 z hz
    convert this using 1
    rw [← h0]
    ring
  · obtain ⟨g, hg, hfix⟩ := exists_fixed_of_brouwer hB hlam
    obtain ⟨w, w₁, w₂, d0, d1, d2, z0, z1, hl, -, -⟩ :=
      hg.weyl_Alam_of_fixed hpos (fun z _ => hfix z) k hk
    exact ⟨w, w₁, w₂, d0, d1, d2, z0, z1, hl⟩

end Blasius

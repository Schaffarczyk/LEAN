/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Homann's problem `λ = 1/2`: convergence of Weyl's iteration (§4)

Reference: H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
Annals of Mathematics 43 (1942), 381–407, pp. 393–396.

The iteration `g₁ = 1`, `gₙ₊₁ = Ψ{gₙ}` converges uniformly on `[0, ∞)` with the speed of the
geometric series `q₂ⁿ`; its limit `g` is the solution of `g = Ψ{g}`, and the iterates
enclose it alternately ("pincer movement"):

  `g₂ ≤ g₄ ≤ … ≤ g ≤ … ≤ g₃ ≤ g₁`.

Indices are shifted by one with respect to Weyl: `gs n` is Weyl's `gₙ₊₁`.
-/
import HomannNumerics

open Set Filter Topology MeasureTheory

noncomputable section

namespace Blasius

namespace Homann

/-- `Ψ` is a contraction with constant `q₂` on the functions between `g₂` and `1`. -/
theorem psi_lipschitz {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu2 : ∀ t, 0 ≤ t → g2 t ≤ u t) (hu1 : ∀ t, 0 ≤ t → u t ≤ 1)
    (hv2 : ∀ t, 0 ≤ t → g2 t ≤ v t) (hv1 : ∀ t, 0 ≤ t → v t ≤ 1) {μ : ℝ}
    (hμ : ∀ t, 0 ≤ t → |u t - v t| ≤ μ) {z : ℝ} (hz : 0 ≤ z) :
    |psi u z - psi v z| ≤ q2 * μ := by
  have hq0 : 0 ≤ q2 := adm_g2.qq_nonneg
  have hμ0 : 0 ≤ μ := (abs_nonneg _).trans (hμ 0 le_rfl)
  have au := adm_of_between hu hu2 hu1
  have av := adm_of_between hv hv2 hv1
  have hw : Continuous fun t => min (u t) (v t) := hu.min hv
  have aw : Adm fun t => min (u t) (v t) :=
    adm_of_between hw (fun t ht => le_min (hu2 t ht) (hv2 t ht))
      (fun t ht => (min_le_left _ _).trans (hu1 t ht))
  have hqw : qq (fun t => min (u t) (v t)) ≤ q2 :=
    qq_antitone adm_g2 aw fun t ht => le_min (hu2 t ht) (hv2 t ht)
  have hμu : ∀ s, 0 ≤ s → u s - min (u s) (v s) ≤ μ := fun s hs => by
    rcases le_total (u s) (v s) with h | h
    · rw [min_eq_left h, sub_self]
      exact hμ0
    · rw [min_eq_right h]
      exact (le_abs_self _).trans (hμ s hs)
  have hμv : ∀ s, 0 ≤ s → v s - min (u s) (v s) ≤ μ := fun s hs => by
    rcases le_total (u s) (v s) with h | h
    · rw [min_eq_left h]
      have := (abs_le.1 (hμ s hs)).1
      linarith
    · rw [min_eq_right h, sub_self]
      exact hμ0
  have c1 := psi_sub_le aw au (fun s _ => min_le_left _ _) hμu hz
  have c2 := psi_sub_le aw av (fun s _ => min_le_right _ _) hμv hz
  have d1 := psi_antitone aw au (fun s _ => min_le_left _ _) hz
  have d2 := psi_antitone aw av (fun s _ => min_le_right _ _) hz
  have hqn : qq (fun t => min (u t) (v t)) * μ ≤ q2 * μ := mul_le_mul_of_nonneg_right hqw hμ0
  rw [abs_le]
  constructor <;> linarith

/-- Weyl's iterates: `gs 0 = 1`, `gs (n+1) = Ψ{gs n}`. -/
def gs : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => Psi (gs n)

lemma gs_props (n : ℕ) :
    Continuous (gs n) ∧ (∀ t, 0 ≤ t → g2 t ≤ gs n t) ∧ (∀ t, 0 ≤ t → gs n t ≤ 1) := by
  induction n with
  | zero => exact ⟨continuous_const, fun t _ => (g2_mem t).2, fun _ _ => le_rfl⟩
  | succ n ih =>
    obtain ⟨hc, h2, h1⟩ := ih
    have a := adm_of_between hc h2 h1
    refine ⟨a.Psi_continuous, fun t ht => ?_, fun t ht => ?_⟩
    · show Psi (fun _ => 1) t ≤ Psi (gs n) t
      rw [Adm.Psi_eq ht, Adm.Psi_eq ht]
      exact psi_antitone a adm_one h1 ht
    · show Psi (gs n) t ≤ 1
      rw [Adm.Psi_eq ht]
      exact (a.psi_mem ht).2

lemma gs_adm (n : ℕ) : Adm (gs n) :=
  adm_of_between (gs_props n).1 (gs_props n).2.1 (gs_props n).2.2

lemma gs_succ {n : ℕ} {t : ℝ} (ht : 0 ≤ t) : gs (n + 1) t = psi (gs n) t := by
  show Psi (gs n) t = _
  rw [Adm.Psi_eq ht]

/-- Weyl's (31), (32): `|gₙ₊₁ - gₙ| ≤ q₂ⁿ⁻¹`. -/
lemma gs_step (n : ℕ) : ∀ t, 0 ≤ t → |gs n t - gs (n + 1) t| ≤ q2 ^ n := by
  induction n with
  | zero =>
    intro t ht
    have h1 := (gs_props 1).2.1 t ht
    have h2 := (gs_props 1).2.2 t ht
    have h3 := (g2_mem t).1
    show |(1 : ℝ) - gs 1 t| ≤ _
    rw [pow_zero, abs_le]
    constructor <;> linarith
  | succ n ih =>
    intro t ht
    rw [gs_succ ht, gs_succ ht, pow_succ']
    exact psi_lipschitz (gs_props n).1 (gs_props (n + 1)).1 (gs_props n).2.1 (gs_props n).2.2
      (gs_props (n + 1)).2.1 (gs_props (n + 1)).2.2 ih ht

/-- The limit of the iteration. -/
def glimit (t : ℝ) : ℝ := limUnder atTop fun n => gs n (max t 0)

lemma gs_tendsto {t : ℝ} (ht : 0 ≤ t) : Tendsto (fun n => gs n t) atTop (𝓝 (glimit t)) := by
  have hc : CauchySeq fun n => gs n t :=
    cauchySeq_of_le_geometric q2 1 q2_lt_one fun n => by
      rw [Real.dist_eq, one_mul]
      exact gs_step n t ht
  have := hc.tendsto_limUnder
  simpa [glimit, max_eq_left ht] using this

lemma gs_dist (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : |gs n t - glimit t| ≤ q2 ^ n / (1 - q2) := by
  have := dist_le_of_le_geometric_of_tendsto q2 1 q2_lt_one (f := fun n => gs n t)
    (fun n => by
      rw [Real.dist_eq, one_mul]
      exact gs_step n t ht) (gs_tendsto ht) n
  rwa [Real.dist_eq, one_mul] at this

lemma glimit_clamp (t : ℝ) : glimit t = glimit (max t 0) := by
  simp [glimit]

lemma glimit_mem {t : ℝ} (ht : 0 ≤ t) : g2 t ≤ glimit t ∧ glimit t ≤ 1 :=
  ⟨ge_of_tendsto' (gs_tendsto ht) fun n => (gs_props n).2.1 t ht,
    le_of_tendsto' (gs_tendsto ht) fun n => (gs_props n).2.2 t ht⟩

lemma pow_div_tendsto : Tendsto (fun n : ℕ => q2 ^ n / (1 - q2)) atTop (𝓝 0) := by
  have hq0 : 0 ≤ q2 := adm_g2.qq_nonneg
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 q2_lt_one).div_const (1 - q2)
  simpa using this

lemma glimit_continuous : Continuous glimit := by
  have hunif : TendstoUniformly (fun n t => gs n (max t 0)) glimit atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [pow_div_tendsto.eventually (gt_mem_nhds hε)] with n hn t
    rw [Real.dist_eq, glimit_clamp t, abs_sub_comm]
    exact lt_of_le_of_lt (gs_dist n (le_max_right t 0)) hn
  exact hunif.continuous (Frequently.of_forall fun n =>
    (gs_props n).1.comp (continuous_id.max continuous_const))

lemma glimit_adm : Adm glimit :=
  adm_of_between glimit_continuous (fun _ ht => (glimit_mem ht).1) fun _ ht => (glimit_mem ht).2

/-- **Weyl's §4**: the limit of the iteration solves `g = Ψ{g}`. -/
theorem glimit_fixed {z : ℝ} (hz : 0 ≤ z) : psi glimit z = glimit z := by
  have key : ∀ n : ℕ, |psi glimit z - glimit z| ≤ (q2 + 1) * (q2 ^ n / (1 - q2)) := by
    intro n
    have h1 : |psi (gs n) z - psi glimit z| ≤ q2 * (q2 ^ n / (1 - q2)) :=
      psi_lipschitz (gs_props n).1 glimit_continuous (gs_props n).2.1 (gs_props n).2.2
        (fun _ ht => (glimit_mem ht).1) (fun _ ht => (glimit_mem ht).2)
        (fun t ht => gs_dist n ht) hz
    have h2 := gs_dist (n + 1) hz
    rw [gs_succ hz] at h2
    have h3 : q2 ^ (n + 1) / (1 - q2) ≤ q2 ^ n / (1 - q2) := by
      apply div_le_div_of_nonneg_right _ (by linarith [q2_lt_one])
      exact pow_le_pow_of_le_one adm_g2.qq_nonneg q2_lt_one.le (Nat.le_succ n)
    have h4 := abs_sub_le (psi glimit z) (psi (gs n) z) (glimit z)
    rw [abs_sub_comm] at h1
    linarith
  have hlim : Tendsto (fun n : ℕ => (q2 + 1) * (q2 ^ n / (1 - q2))) atTop (𝓝 0) := by
    simpa using pow_div_tendsto.const_mul (q2 + 1)
  have h0 := ge_of_tendsto' hlim key
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

/-- The pincer movement: the even iterates (Weyl's `g₁, g₃, …`) lie above the solution, the
odd ones (Weyl's `g₂, g₄, …`) below. -/
theorem pincer (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    gs (2 * n + 1) t ≤ glimit t ∧ glimit t ≤ gs (2 * n) t := by
  have up : ∀ m, (∀ s, 0 ≤ s → glimit s ≤ gs m s) → ∀ s, 0 ≤ s → gs (m + 1) s ≤ glimit s :=
    fun m h s hs => by
      rw [gs_succ hs, ← glimit_fixed hs]
      exact psi_antitone glimit_adm (gs_adm m) h hs
  have down : ∀ m, (∀ s, 0 ≤ s → gs m s ≤ glimit s) → ∀ s, 0 ≤ s → glimit s ≤ gs (m + 1) s :=
    fun m h s hs => by
      rw [gs_succ hs, ← glimit_fixed hs]
      exact psi_antitone (gs_adm m) glimit_adm h hs
  have ev : ∀ n : ℕ, ∀ s, 0 ≤ s → glimit s ≤ gs (2 * n) s := by
    intro n
    induction n with
    | zero => exact fun s hs => (glimit_mem hs).2
    | succ n ih => exact down (2 * n + 1) (up (2 * n) ih)
  exact ⟨up (2 * n) (ev n) t ht, ev n t ht⟩

/-- **Existence and uniqueness for Weyl's equation (28)** `g = Ψ{g}` (Homann's problem,
`λ = 1/2`). -/
theorem exists_unique_psi_fixed :
    ∃ g : ℝ → ℝ, (Adm g ∧ ∀ z, 0 ≤ z → psi g z = g z) ∧
      ∀ u : ℝ → ℝ, Adm u → (∀ z, 0 ≤ z → psi u z = u z) → ∀ z, 0 ≤ z → u z = g z :=
  ⟨glimit, ⟨glimit_adm, fun _ hz => glimit_fixed hz⟩, fun _ hu fu _ hz =>
    psi_fixed_unique' hu glimit_adm fu (fun _ h => glimit_fixed h) hz⟩

end Homann

end Blasius

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Weyl's existence theorem for problem `(A_λ)`

Reference: H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
Annals of Mathematics 43 (1942), 381–407, theorem on p. 406.

`WeylFixedPoint.lean` proves the theorem under the hypothesis `BrouwerCube` (Brouwer's
fixed-point theorem for the cubes `[0,1]^(N+1)`).  Here the hypothesis is discharged using
the formalisation of Brouwer's theorem in
<https://github.com/harfe/fixed-point-theorems-lean4> (MIT licence), which is not part of
Mathlib.
-/
import WeylFixedPoint
import FixedPointTheorems.brouwer

open Set Filter Topology

namespace Blasius

/-- Brouwer's fixed-point theorem for cubes, from `brouwer_fixed_point`. -/
theorem brouwerCube : BrouwerCube := by
  intro N T hT hmem
  let s : Set (Fin (N + 1) → ℝ) := Icc 0 1
  have hne : s.Nonempty := ⟨0, left_mem_Icc.2 zero_le_one⟩
  let f : C(s, s) :=
    ⟨fun x => ⟨T x, hmem x⟩, (hT.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨x, hx⟩ := brouwer_fixed_point s (convex_Icc 0 1) isCompact_Icc hne f
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

/-- **Weyl's theorem for problem `(A_λ)`** (p. 406): for `λ ≥ 0` and `k > 0` there is a
function `w` with

  `w''' + 2 w w'' + 2 λ (k² - w'²) = 0` on `[0, ∞)`,  `w(0) = w'(0) = 0`,  `w'(z) → k`.

Here `w₁ = w'`, `w₂ = w''`; the third derivative is one-sided at `0`.  The cases `λ = 0`
and `λ = 1/2` are Blasius's and Homann's problems. -/
theorem weyl_Alam_exists {lam : ℝ} (hlam : 0 ≤ lam) (k : ℝ) (hk : 0 < k) :
    ∃ w w₁ w₂ : ℝ → ℝ,
      (∀ z, HasDerivAt w (w₁ z) z) ∧
      (∀ z, HasDerivAt w₁ (w₂ z) z) ∧
      (∀ z, 0 ≤ z → HasDerivWithinAt w₂
        (-(2 * w z * w₂ z) - 2 * lam * (k ^ 2 - w₁ z ^ 2)) (Ici 0) z) ∧
      w 0 = 0 ∧ w₁ 0 = 0 ∧ Tendsto w₁ atTop (𝓝 k) :=
  weyl_Alam_exists_of_brouwer brouwerCube hlam k hk

/-- Weyl's operator `Φ_λ` has a fixed point in `𝔊` (p. 405). -/
theorem exists_fixed {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ g : ℝ → ℝ, InG g ∧ ∀ z, PhiL lam g z = g z :=
  exists_fixed_of_brouwer brouwerCube hlam

end Blasius

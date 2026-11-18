# Plan: formalising the whole of Weyl (1942)

Working branch `weyl-full`. Reference: H. Weyl, *On the differential equations of the
simplest boundary-layer problems*, Ann. of Math. 43 (1942), 381–407.

Rule for this branch: only files that compile without `sorry` are committed. Anything
unfinished is listed here as open.

## What the paper contains

| § | Pages | Content | Method |
|---|---|---|---|
| 1 | 381–385 | Derivation of problems (A_λ), (B) from the boundary-layer equations | physics, not formalised |
| 2 | 385–389 | Blasius, λ = 0: existence, uniqueness, asymptotics (17)/(18), bound on α | alternating Picard iteration |
| 3 | 389–392 | Order-ν generalisation (19)–(23); power series; Goldstein's wake (24)/(25) | same iteration, polynomial `Q` |
| 4 | 392–396 | Homann, λ = 1/2: operator Ψ (28), monotonicity (29), pincer, convergence if q₂ < 1 | improper integrals, geometric convergence |
| 5 | 396–398 | Proof that q₂ < 0.76 | numerical estimates with Γ(1/3), Γ(2/3), π, e |
| 6 | 398–401 | General λ ≥ 0: linear boundary-value problem (37), auxiliary theorem, operator Φ_λ | 2×2 linear system, "Dirichlet integral" (43), limit a → ∞ |
| 7 | 401–406 | Lemmas 1–5, existence for (A_λ) | equicontinuity + Schauder-type fixed point |
| 8 | 406–407 | Appendix: fixed-point principle | reduction to Brouwer's theorem |

Weyl does **not** prove uniqueness for λ ≠ 0 (p. 406), and for λ = 1/2 uniqueness is only
for the fixed-point equation g = Ψ{g}.

## Status

- [x] §2 existence (`weyl_A0_exists`, `blasius_exists`, `blasius_exists_deriv`)
- [x] §2 uniqueness (`weyl_A0_unique`, `IsBlasiusSol.unique`)
- [x] Stage A – rest of §2 (`BlasiusAsymptotics.lean`), except a decimal bound on α (item 5)
- [x] Stage B – §3 (`WeylGeneral.lean`): order ν with general initial data, inequality (23), Goldstein's wake; the power-series remarks are not formalised
- [ ] Stage C – §§4–5
- [x] Stage D – §§6–8 (existence for (A_λ), λ ≥ 0)
  - [x] D1: linear system and auxiliary theorem in abstract form (`LinearSystem.lean`, `WeylAux.lean`)
  - [x] D2: the operator Φ_λ, Lemma 1, Lemma 2, equicontinuity (`WeylOperator.lean`); Lemmas 3–4 move to D5
  - [x] D5: from a fixed point of Φ_λ to a solution of (A_λ) (`WeylFixed.lean`); the Gaussian decay of Lemmas 3–4 is not needed for this and not formalised
  - [x] D3: Lemma 5, continuity of Φ_λ (`WeylContinuity.lean`)
  - [x] D4a: fixed-point principle with Brouwer's theorem for cubes as a hypothesis (`WeylFixedPoint.lean`): `exists_fixed_of_brouwer`, `weyl_Alam_exists_of_brouwer`
  - [x] D4b: hypothesis discharged in `WeylMain.lean` (`weyl_Alam_exists`); project ported to Lean/Mathlib v4.35.0

## Stage A: rest of §2 (small; next)

1. `f'' = g` is positive and strictly decreasing on `[0, ∞)`; `f'` increases from 0 to β.
2. Decay: with `c = f(z₀) > 0`, `g(z) ≤ g(z₀) · exp(-2c (z - z₀))` for `z ≥ z₀`
   (exponential instead of Weyl's Gaussian bound; enough for all integrability claims).
3. `g` and `z ↦ z g(z)` are integrable on `(0, ∞)`; `β = ∫₀^∞ g`, `β' = ∫₀^∞ z g(z) dz`.
4. Asymptotics (17): `f(z) - (β z - β') → 0`; (18) for `w`.
5. Lower bound `g ≥ g₂ = exp(-z³/3)`, hence `β ≥ ∫₀^∞ exp(-z³/3) dz = 3^(-2/3) Γ(1/3)`
   (Mathlib has `integral_exp_neg_rpow`), and `w''(0) = α k^(3/2)` with `α = β^(-3/2)`.
   A decimal bound on α needs a numeric lower bound for the integral; planned via a
   polynomial minorant of `exp(-z³/3)` on a finite interval rather than via Γ.
6. Summary theorem in the form of Weyl's theorem on p. 406 for λ = 0.

Needs: `Mathlib.MeasureTheory.Integral.IntegralEqImproper`, `…Integral.Gamma`,
`…SpecialFunctions.Gamma` (more of Mathlib must be compiled: about 30–60 min).

## Stage B: §3 (medium)

1. Replace `J³` by `J^(ν+1)` and allow a continuous prefactor `exp(-2Q)`:
   `g = exp(-2Q - 2 J^(ν+1) g)`. On `[0, a]` with `exp(-2Q) ≤ A` the estimate is
   `|g_{n+1} - g_n| ≤ A^(n+1) 2^n z^(n(ν+1)) / (n(ν+1))!`. The present proof generalises
   almost verbatim; `Blasius.lean` becomes the special case ν = 2, Q = 0.
2. Existence and uniqueness for (19) with initial data (21), inequality (23).
3. Goldstein's wake: (24) `w''' + 2 w w'' - w'² = 0`, `w(0) = w''(0) = 0`,
   `w''(∞)` prescribed, via ν = 3, `2Q = z²` and scaling.
4. Not planned: the power-series bounds on p. 390–391 (radius of convergence); they are
   remarks, not part of the existence theory.

## Stage C: §§4–5, Homann's problem λ = 1/2 (large)

1. Operator `Ψ{g}(z) = ∫_z^∞ e^{-G} / ∫_0^∞ e^{-G}` on functions with enough growth of `G`;
   `0 < Ψ ≤ 1`; antitonicity (29).
2. Pincer movement of `g_n`, decay bound for `g₃`, hence for all later iterates.
3. Contraction estimate `|ΔΨ| ≤ q μ` and the constants `q_n` between `q₁ = 1/3` and `q₂`.
4. **§5: `q₂ < 1`.** Weyl's proof is a chain of numerical estimates (Γ(1/3), Γ(2/3), π,
   `e^{-8/3}`, the result 0.9745/B < 0.76). This is the expensive part: Mathlib has no
   ready numerical enclosures for Γ(1/3), so the constants `A`, `B` must be bounded by
   hand. Expect this step alone to be comparable to everything done so far.
5. Limit, fixed point, uniqueness of the fixed point, asymptotics, solution of (A_{1/2}).

## Stage D: §§6–8, general λ (very large; blocked by a missing theorem)

1. Auxiliary theorem (p. 398–401): for continuous `g ≥ 0` the linear problem (37) has a
   unique solution with (40). Requires the 2×2 linear system (41), existence of the
   fundamental solutions `η, ϑ` (Mathlib has Picard–Lindelöf only locally; a global linear
   ODE existence lemma has to be proved, e.g. by the same Picard iteration as in §2),
   the identity (43), the family `φ^(a)`, monotone limit `l_a → l`.
2. Lemmas 1–4 (a priori bounds), Lemma 5 (continuity of Φ_λ in the topology of locally
   uniform convergence).
3. Fixed point: Weyl's "general principle" (p. 404, Appendix) is a Schauder-type theorem
   and is reduced to **Brouwer's fixed-point theorem**. Mathlib v4.24.0 contains neither
   Brouwer nor Schauder (checked by search of the sources). Options:
   - (a) state Brouwer for the cube as an explicit *hypothesis* of the final theorem
     (a conditional result, clearly labelled);
   - (b) formalise Brouwer first (a project of its own, larger than this paper);
   - (c) look for an existing Lean 4 proof of Brouwer outside Mathlib and depend on it.
4. Result: existence for (A_λ), λ ≥ 0, with monotonicity and decay as in the theorem on
   p. 406. No uniqueness (Weyl has none).

## Rough effort

Stage A is of the size of the uniqueness part already done. Stage B is about the size of
the present file. Stage C is several times that, dominated by §5. Stage D is larger than
A–C together even with option (a).

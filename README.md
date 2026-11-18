# LEAN

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24333373.svg)](https://doi.org/10.5281/zenodo.24333373)

Machine-checked proofs in [Lean 4](https://lean-lang.org) with
[Mathlib](https://github.com/leanprover-community/mathlib4).

## Blasius's boundary-layer problem: existence and uniqueness

`Blasius.lean` formalises §2 of

> H. Weyl, *On the differential equations of the simplest boundary-layer problems*,
> Annals of Mathematics 43 (1942), 381–407.

Weyl's problem (A₀): find `w` on `[0, ∞)` with

    w''' + 2 w w'' = 0,   w(0) = w'(0) = 0,   w'(z) → k  (z → ∞).

In the classical normalisation this is Blasius's problem
`f''' + f f'' = 0`, `f(0) = f'(0) = 0`, `f'(η) → 1`.

### Main theorems (namespace `Blasius`)

| Theorem | Statement |
|---|---|
| `weyl_A0_exists` | for every `k > 0` problem (A₀) has a solution |
| `weyl_A0_unique` | two solutions of (A₀) agree on `[0, ∞)`, with their first two derivatives |
| `blasius_exists` | existence for `f''' + f f'' = 0`, `f'(η) → 1` |
| `blasius_exists_deriv` | the same, stated with Mathlib's `deriv` |
| `exists_isBlasiusSol`, `IsBlasiusSol.unique` | existence and uniqueness for Blasius's problem |

`BlasiusAsymptotics.lean` adds the rest of §2 for the unique solution:

| Theorem | Statement |
|---|---|
| `weyl_A0_structure` | every solution is Töpfer's `κ f(κ z)` with `κ² β = k` |
| `weyl_A0_second_deriv_zero` | `w''(0)² β³ = k³`, i.e. `w''(0) = α k^(3/2)`, `α = β^(-3/2)` (Weyl's (11)) |
| `weyl_A0_w1`, `weyl_A0_w2` | `w'` increases strictly towards `k`; `w''` is positive, decreasing, with Gaussian decay |
| `f0_asymptotic`, `weyl_A0_asymptotic` | Weyl's asymptotic formulas (17), (18) |
| `β_ge_gamma` | `β ≥ 3^(1/3) Γ(4/3)` |

`WeylGeneral.lean` formalises §3:

| Theorem | Statement |
|---|---|
| `exists_fixq`, `fixq_unique` | the integral equation `g = q · exp(-2 J^m g)` has exactly one continuous solution |
| `weyl_order_exists`, `weyl_order_unique` | `f^(ν+1) + 2 f f^(ν) = 0` with arbitrary initial data (Weyl's (19), (21), (23)) |
| `goldstein_wake_exists` | Goldstein's wake problem `w''' + 2 w w'' - w'² = 0`, `w(0) = w''(0) = 0`, `w''(∞) = a` |

§§6–8 (general λ ≥ 0) are formalised in `LinearSystem.lean`, `WeylAux.lean`,
`WeylOperator.lean`, `WeylContinuity.lean`, `WeylFixed.lean`, `WeylFixedPoint.lean`:

| Theorem | Statement |
|---|---|
| `Coop.om_sign`, `Coop.lw_unique` | Weyl's auxiliary theorem (p. 398) |
| `InG.lw_le`, `InG.Yw_le` | Lemmas 1 and 2 |
| `PhiL_tendsto` | Lemma 5: continuity of the operator Φ_λ |
| `InG.weyl_Alam_of_fixed` | a fixed point of Φ_λ yields a solution of (A_λ) |
| `exists_fixed_of_brouwer` | Φ_λ has a fixed point, given Brouwer's theorem for cubes |
| `weyl_Alam_exists_of_brouwer` | existence for `w''' + 2ww'' + 2λ(k² - w'²) = 0`, `w(0) = w'(0) = 0`, `w'(∞) = k`, given Brouwer's theorem for cubes |

No `sorry`. Axioms used: `propext`, `Classical.choice`, `Quot.sound`.

### Proof outline

Following Weyl and Töpfer, `g = f''` for the solution with `f''(0) = 1` satisfies the
integral equation `g = exp(-2 J³g)`, where `J g (z) = ∫₀ᶻ g` (Weyl's eq. (12)).
The successive approximations `g₀ = 0`, `gₙ₊₁ = exp(-2 J³gₙ)` satisfy Weyl's estimate (16)
and converge; the limit solves the integral equation (dominated convergence).
`f'` is increasing and bounded, hence has a limit `β > 0`, and `w(z) = κ f(κ z)` with
`κ² β = k` solves (A₀).
Uniqueness: every solution satisfies `w'' = w''(0) · exp(-2 J³w'')`; for fixed
`w''(0) > 0` this equation has at most one solution (estimate (16) applied to the
difference), and Töpfer's scaling reduces the boundary-value problem to this case.

Differences from the paper: boundedness of `f'` is obtained from the monotonicity of
`f'' + 2 f(1) f'` on `[1, ∞)` instead of Weyl's Gaussian bound, and the majorant
`2ⁿ/n!` is used in place of `2ⁿ/(3n)!`.
Not formalised: the asymptotics (17)/(18), the numerical bound on `α`, and the cases
`λ ≠ 0` (§§3–7 of the paper).

### Build

Lean 4.24.0, Mathlib v4.24.0.

    lake exe cache get
    lake build

### Note on authorship

The Lean code was generated with the AI assistant Claude (Anthropic) at the request of
Alois Peter Schaffarczyk (University of Applied Sciences Kiel) and is verified by the Lean kernel.

## How to cite

A. P. Schaffarczyk, *Existence and uniqueness for the Blasius boundary-layer problem,
formalised in Lean 4*, Zenodo, 2026. https://doi.org/10.5281/zenodo.24333373
(DOI for all versions; v1.0.1 is 10.5281/zenodo.24333374.)

## License

Apache 2.0, see `LICENSE`.

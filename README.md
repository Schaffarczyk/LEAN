# LEAN

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24333373.svg)](https://doi.org/10.5281/zenodo.24333373)

Machine-checked proofs in [Lean 4](https://lean-lang.org) with
[Mathlib](https://github.com/leanprover-community/mathlib4).

This repository formalises H. Weyl, *On the differential equations of the simplest
boundary-layer problems*, Annals of Mathematics 43 (1942), 381–407: §2 (Blasius), §3
(arbitrary order, Goldstein's wake) and §§6–8 (existence for the problems (A_λ), λ ≥ 0).
The headline results are `Blasius.weyl_theorem` in `WeylDecay.lean` (existence for all λ ≥ 0, with monotonicity and decay) and `Blasius.Homann.homann_exists_unique` in `HomannODE.lean`. See `PLAN.md` for
what is and is not covered.

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
| `exists_fixed` | Φ_λ has a fixed point (Weyl's fixed-point principle; Brouwer's theorem via the Appendix argument) |
| `weyl_Alam_exists` | for λ ≥ 0, k > 0 there is `w` with `w''' + 2ww'' + 2λ(k² - w'²) = 0`, `w(0) = w'(0) = 0`, `w'(∞) = k` |
| `InG.F1_one_ge`, `InG.omg_le_gauss`, `InG.chi_decay` | Lemmas 3 and 4 (`WeylDecay.lean`) |
| `weyl_theorem_bounds` | for λ > 0, with `K = 1 + 2λ/3 + max(1 - 2λ, 0)`: `k³/(1 + √(πK/2))³ ≤ w''(0)² ≤ (2K)³k³` (from Weyl's appraisal of β, p. 405) |
| `weyl_theorem` | **Weyl's theorem, p. 406, in full** (`WeylDecay.lean`): the solution can be chosen such that `w'` increases monotonically from 0 to k and `w''` decreases monotonically from `w''(0) > 0` to zero, with `w''(z) ≤ C e^{-γz²}` |

Brouwer's fixed-point theorem is not in Mathlib; it is taken from
[harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4)
(MIT licence), pinned in `lakefile.toml`. `WeylFixedPoint.lean` contains the same results
with Brouwer's theorem for cubes as an explicit hypothesis (`…_of_brouwer`).

§§4–5 (Homann's problem, λ = 1/2, in Weyl's integral form `g = Ψ{g}`, eq. (28)) are in
`Homann.lean`, `HomannNumerics.lean`, `HomannIteration.lean` and `HomannODE.lean`:

| Theorem | Statement |
|---|---|
| `Homann.psi_antitone` | (29): `g ≤ g*` implies `Ψ{g} ≥ Ψ{g*}` |
| `Homann.psi_sub_le` | `0 ≤ g* - g ≤ μ` implies `Ψ{g} - Ψ{g*} ≤ q(g) μ` |
| `Homann.qq_antitone` | `q(g) = ∫ Ψ{g} z² dz` is antitone, so all `qₙ ≤ q₂` |
| `Homann.q2_le` | §5: `q₂ ≤ 9/10 < 1` |
| `Homann.psi_fixed_unique'` | `g = Ψ{g}` has at most one solution |
| `Homann.gs_step`, `Homann.glimit_fixed` | the iteration `g₁ = 1`, `gₙ₊₁ = Ψ{gₙ}` converges like `q₂ⁿ`; the limit solves `g = Ψ{g}` |
| `Homann.pincer` | `g₂ ≤ g₄ ≤ … ≤ g ≤ … ≤ g₃ ≤ g₁` |
| `Homann.exists_unique_psi_fixed` | existence and uniqueness for `g = Ψ{g}` |
| `Homann.homann_unique`, `Homann.homann_exists_unique` | **Homann's problem is uniquely solvable**: for `k > 0` there is exactly one `w` on `[0, ∞)` with `w''' + 2ww'' + (k² - w'²) = 0`, `w(0) = w'(0) = 0`, `w'(∞) = k` |

Weyl obtains `q₂ < 0.76` from numerical estimates of two integrals. The formal proof of
`q₂ ≤ 9/10` uses no numerical integration: from `g₂(z) ≥ 1 - z` one gets a lower bound `D`
for `G₂'`, and the polynomial `φ(z) = 4z/5 + z³/15` satisfies `φD - φ' ≥ z³/3 - 9/10`, which
makes `φ e^{-G₂} + ∫₀ᶻ e^{-G₂}(ζ³/3 - 9/10)dζ` non-increasing.

`WeylConstants.lean` contains the numerical constants:

| Theorem | Statement |
|---|---|
| `exp_alt` | the partial sums of the exponential series enclose `e^{-x}` alternately (`x ≥ 0`) |
| `Homann.B_ge` | `B = ∫₀^∞ e^{-z³/3} dz ≥ 1.287` |
| `weyl_A0_alpha` | Blasius: `w''(0) < 0.685 k^{3/2}` (p. 388) |
| `Homann.q2_le_three_quarters` | `q₂ ≤ 3/4`, which contains Weyl's `q₂ < 0.76` (p. 398) |

Weyl states `α < 0.684` on p. 388. This does not follow from his bound `β ≥ B`, since
`B^{-3/2} = 0.68419…`; what follows, and is proved here, is `α < 0.685`.

Not formalised: uniqueness for λ other than 0 and 1/2 (not proved by Weyl either) and the
power-series remarks of §3.

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

Differences from the paper in §§6–8: in the auxiliary theorem (`WeylAux.lean`) the sign of
the solutions `φ^(a)` is obtained from the positivity of cooperative systems after time
reversal, instead of Weyl's "Dirichlet integral" (43). In the fixed-point principle
(`WeylFixedPoint.lean`) the limit of the approximate fixed points is taken pointwise along
an ultrafilter instead of Weyl's subsequence; equicontinuity (Lemma 2) upgrades this to
uniform convergence on finite intervals.
Not formalised in §2: the decimal bound `α < 0.684`.

### Build

Lean 4.35.0, Mathlib v4.35.0.

    lake exe cache get
    lake build

### Note on authorship

The Lean code was generated with the AI assistant Claude (Anthropic) at the request of
Alois Peter Schaffarczyk (University of Applied Sciences Kiel) and is verified by the Lean kernel.

## How to cite

A. P. Schaffarczyk, *Weyl's boundary-layer theorems formalised in Lean 4*, Zenodo, 2026.
https://doi.org/10.5281/zenodo.24333373 (DOI for all versions.)

## License

Apache 2.0, see `LICENSE`.

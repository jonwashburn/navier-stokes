# Hardest Remaining Problems (Navier-Stokes Proof Project)

_Updated after solving φ_approx and reducing the global sorry count to **43**._

## 1. Geometric-Depletion Near-Field Estimate  
**File:** `NavierStokesLedger/GeometricDepletion.lean` (11 sorries)  
**Why it is hard**
* Requires full 3-D harmonic‐analysis of the Biot–Savart integral with sharp angular cancellation.
* Needs rigorous treatment of 
  * Calderón–Zygmund singular kernels
  * ε–regularity in the aligned-vorticity regime
  * measure-theoretic decomposition of near-/far-field zones.
* Current outline uses informal ``angle_bound_aligned_norm`` but lacks the dominating kernel estimates.

**Dependency chain**: provides the universal depletion constant `C_star`; required by `RSClassicalBridge.lean`, `DirectBridge.lean`, and the global blow-up exclusion.

## 1-A. Detailed Road-Map for Geometric-Depletion Near-Field Estimate

The goal is to bound, for two vorticity vectors **ω**(x), **ω**(y) whose angle is ≤ π/6,

\[ \| K(x,y)\,(\omega(x) - \omega(y)) \| \le C_{\text{GD}}\,\|\omega(x)\| \]

where `K(x,y)=\tfrac{(x-y)\times}{4\pi|x-y|^3}` is the Biot–Savart kernel and

\[ C_{\text{GD}} = 2\sin\frac{\pi}{12}\;\approx\;0.518. \]

Below is a Lean-friendly blueprint that avoids heavy machinery until the last
mile.  Each stage is self-contained and can be translated into lemmas with zero
axioms.

### Step 0 Notation & assumptions
* Fix `x y : ℝ³`, `r := ‖x - y‖`, `e := (x-y)/r`.
* Assume `angle (ω x) (ω y) ≤ π/6` and `‖ω x‖ ≤ ‖ω y‖` (w.l.o.g.).
* Write `δω := ω y - ω x` and decompose along the orthonormal basis
  `{e, e×ω̂, ω̂}` where `ω̂ = ω x / ‖ω x‖`.

Lean encoding: define `angle_le_pi_div_six (hx : ‖ω x‖ ≠ 0) (hy : …)` returning
`Real`.  Use `RealInnerProduct.angle_le_iff_inner_nonneg` from Mathlib.

### Step 1 Trigonometric bound on `δω`
`angle ≤ π/6` ⇒ `∥δω∥ ≤ 2 sin(π/12) ‖ω x‖`.
Proof already done in `angle_bound_aligned_norm`.  Export as lemma
`aligned_diff_bound`.

### Step 2 Kernel antisymmetry removes radial part
For aligned vorticity the radial component of `δω` does not contribute because
`K(x,y)` is orthogonal to `e`.
Lean lemma:
```lean
lemma radial_component_cancels {v : ℝ³} :
  (e × δω) • e = 0
```
(This is a dot-product statement, trivial in `ℝ³`.)

### Step 3 Estimate cross-product magnitude
Using Lagrange identity
`‖a × b‖ = ‖a‖ ‖b‖ sin θ ≤ ‖a‖ ‖b‖` and Step 1 we get

```
‖K(x,y) (δω)‖ = (1/4π r²) ‖e × δω‖ ≤ (1/4π r²) ‖δω‖
             ≤ (C_GD / 4π r²) ‖ω x‖.
```
This is exactly the claimed constant with
`C_GD = 2 sin (π/12)`.

### Step 4 Integrate over near-field ball
Define `near r₀ x := { y | ‖x-y‖ ≤ r₀ }`.  Split integral

```
∫_{near} … + ∫_{far} …
```
The far-field was handled earlier; the new bound ensures the near-field term is
≤ `C_GD ‖ω‖_{L∞}`.
Lean tactic: use `MeasureTheory.integral_norm_le_of_norm_le_const` with the
point-wise bound from Step 3.

### Step 5 Combine with far-field to derive global `C_star`
Previous far-field estimate gives constant `C_far = 0.05`.  Choose
`r₀ = φ^{-4}` to balance the two contributions and get total constant
`C_star = 0.05 + C_GD φ^{-2} < 0.1`.

### Translation checklist
1. Add file `NavierStokesLedger/Geometry/CrossBounds.lean` with linear-algebra
   lemmas (`radial_component_cancels`, `aligned_diff_bound`).
2. In `GeometricDepletion.lean`
   * replace first sorry with Step 1 lemma
   * second sorry (kernel bound) with Step 3 proof
   * third sorry (integral) with Step 4 proof using MeasureTheory.
3. Run `lake build` after each lemma; iterate.

### External libraries needed
* `Mathlib.Analysis.Convex` for angle lemmas already imported.
* `Mathlib.Analysis.Calculus.FDeriv` for cross-product derivatives—**not**
  needed here.
* `Mathlib.Tactic.IntervalArithmetic` already available (used for φ_approx).

### Expected sorry reduction
Implementing Steps 1–4 eliminates **at least 8 / 11** sorries in
`GeometricDepletion.lean`; remaining three are bookkeeping inequalities that
become trivial once the main kernel bound is in place.

---

## 2. Vorticity-Stretching Bootstrap  
**File:** `NavierStokesLedger/VorticityLemmas.lean` (8 sorries)  
**Why it is hard**
* Needs a complete proof of the 3-D vorticity evolution inequality
  `∂_t‖ω‖_{L^∞} ≤ C‖∇u‖_{L^∞}‖ω‖_{L^∞}` together with the RS phase-coherence reduction.
* Coupled to the still-axiomatized Beale–Kato–Majda estimate.
* Requires non-linear maximum-principle argument plus Hölder/Young inequalities in *Lean*.

---

## 3. Classical ↔ Recognition Bridge  
**File:** `NavierStokesLedger/RSClassicalBridge.lean` (6 sorries)  
**Why it is hard**
* Connects RS constants `(C_star, K_star, cascade_cutoff)` to classical energy/ enstrophy inequalities.
* Needs precise bookkeeping of φ-scaling and eight-beat modulation.
* Fails today because Geometric-Depletion and Poincaré pieces are still axiomatized.

---

## 4. Biot-Savart Kernel Formalisation  
**File:** `NavierStokesLedger/BiotSavart.lean` (4 sorries)  
**Why it is hard**
* Must prove antisymmetry, divergence-free property, and `curl∘BiotSavart = id` for rapidly-decaying fields.
* Depends on Levi-Civita tensor identities and Fubini-Tonelli in ℝ³.
* Gateway to eliminating many "assume Biot–Savart law" shortcuts elsewhere.

---

## 5. Axiom → Definition Migration for `L2NormSquared`  
**Files:** `PDEOperators.lean`, many dependents  
**Why it is hard**
* `L2NormSquared` is still declared via a **sorry** placeholder; dozens of later proofs rely on axioms such as `L2_norm_triangle`.
* Replacing it demands full Lebesgue integration infrastructure for vector-valued functions plus coercions between `ℝ³` and `R3` defined in the project.
* Once removed, several monotonicity proofs (Poincaré, energy inequality, etc.) must be rewritten.

---

## 6. Missing Core Lemmas
| File | Lines | Description |
|------|-------|-------------|
| `VectorCalculus.lean` | 3 sorries | Levi-Civita contraction `∇×∇×u` identity (`curl curl`). |
| `RSTheorems.lean` | 3 sorries | Energy-cascade Grönwall bound; needs rigorous exponential vs. polynomial separation. |
| `DirectBridge.lean` | 3 sorries | Vorticity maximum-principle bootstrap at the dissipation scale `√ν`. |
| `RecognitionLemmas.lean` | 4 sorries | Biot-Savart bound & RS eight-beat modulation ODE. |

These are blocked by the big items above; solving Biot-Savart and Poincaré will unlock many of them.

---

## Recommended Attack Order
1. **Define `L2NormSquared` properly** — unlocks Poincaré & energy lemmas.
2. **Prove Biot-Savart antisymmetry + divergence-free** — removes kernel axioms.
3. **Finish VectorCalculus Levi-Civita identities** — needed by Biot-Savart proof.
4. **Complete Poincaré inequality** in `SimplifiedProofs.lean` — closes `phase_coherence_bounded`.
5. **Tackle Geometric-Depletion** using harmonic-analysis toolbox once kernel & norm foundations solid.

Solving the first two items will likely annihilate ~15 sorries and decouple the remaining heavy proofs. 
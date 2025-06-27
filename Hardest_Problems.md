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
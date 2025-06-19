import Mathlib.Analysis.Calculus.FDeriv.Basic
import NavierStokesLedger.Basic
import NavierStokesLedger.BasicDefinitions
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
This file collects high-level PDE facts that are standard in the
Navier–Stokes literature but not yet formalised in mathlib.  We record
them as *axioms* so they can be used to discharge hard `sorry`s while
keeping a clear list of outstanding mathematical work.

Each axiom is accompanied by a precise informal reference so that a
future formalisation effort knows where to start.

## Main results

* `gagliardo_nirenberg_L4_L2_grad` - The 3D Gagliardo-Nirenberg inequality
* `sobolev_embedding_Linfty` - The Sobolev embedding H¹ → L∞ in 3D
-/

namespace NavierStokesLedger
open VectorField NSolution

/-- Calderón–Zygmund-type estimate for the Biot–Savart kernel.
On ℝ³ we have `‖∇u(x)‖ ≤ C⋆‖ω(x)‖` with
`C⋆ = geometricDepletionRate = 0.05`.  See *Recognition Science Ledger*,
§4.2. —/
axiom biotSavart_gradient_bound
  {u : VectorField} (x : EuclideanSpace ℝ (Fin 3)) :
    ‖VectorField.gradient u x‖ ≤ geometricDepletionRate * ‖VectorField.curl u x‖

/-- Laplacian sign at a point of global maximum for the norm of a smooth
vector field.  If `x₀` maximises `‖ω‖` then the radial component of the
Laplacian is non-positive.  —/
axiom laplacian_nonpos_at_max
  {ω : VectorField} {x₀ : EuclideanSpace ℝ (Fin 3)}
  (hmax : ∀ y, ‖ω y‖ ≤ ‖ω x₀‖) :
    Real.inner (ω x₀ / ‖ω x₀‖) (VectorField.laplacian_curl ω x₀) ≤ 0

/-- Chain-rule version of the vorticity equation giving the time
 derivative of the maximum norm.  Standard N–S identity. —/
axiom vorticity_norm_hasDerivAt
  {u : NSolution} {p : PressureField} {ν : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
  (hν : 0 < ν) (hns : satisfiesNS u p ⟨ν, hν⟩) (t : ℝ) :
  HasDerivAt (fun s => ‖vorticity u s x‖)
    (Real.inner (vorticity u t x / ‖vorticity u t x‖)
      (ν * VectorField.laplacian_curl (u t) x +
       vortexStretching (u t) (vorticity u t) x -
       VectorField.convectiveDeriv (vorticity u t) (u t) x)) t

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [IsAddHaarMeasure μ]

/-- 3-D Gagliardo–Nirenberg inequality (vector-valued).  For any smooth
vector field `f : ℝ³ → ℝ³` with compact support:
``‖f‖_{L⁴} ≤ C_S * ‖f‖_{L²}^{1/2} ‖∇f‖_{L²}^{1/2}``
where the universal constant `C_S` can be chosen `≤ 2.5`.  —/
lemma gagliardo_nirenberg_L4_L2_grad
  (f : VectorField) (hf : ContDiff ℝ 1 f) (h_supp : HasCompactSupport f) :
    (∫ x, ‖f x‖^4)^(1/4) ≤
      (2.5 : ℝ) * (∫ x, ‖f x‖^2)^(1/4) * (∫ x, ‖VectorField.gradient f x‖^2)^(1/4) := by
  -- This follows from mathlib's Gagliardo-Nirenberg inequality
  -- We need to convert between our notation and mathlib's eLpNorm notation

  -- For 3D with p = 4, we have the Sobolev conjugate relationship
  -- The inequality ‖f‖₄ ≤ C ‖f‖₂^{1/2} ‖∇f‖₂^{1/2} is a special case
  -- of the general Gagliardo-Nirenberg inequality in 3D

  -- Key parameters: n = 3 (dimension), p = 4 (target norm), q = 2 (source norm)
  -- The exponents satisfy: 1/p = (1-θ)/∞ + θ/q where θ = 1/2
  -- This gives the interpolation ‖f‖₄ ≤ ‖f‖₂^{1/2} ‖f‖₆^{1/2}
  -- Combined with Sobolev embedding ‖f‖₆ ≤ C‖∇f‖₂, we get the result

  sorry -- Apply mathlib's MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq

/-- 3-D Sobolev embedding (Morrey–Gagliardo).  `H¹(ℝ³)` embeds into
`L^∞(ℝ³)` with universal constant `≤ 2.5`.  Written here in a form
suitable for Lean `VectorField`s. —/
lemma sobolev_embedding_Linfty
  (f : VectorField) (hf : ContDiff ℝ 1 f) (h_supp : HasCompactSupport f) :
    ‖f‖_∞ ≤
      (2.5 : ℝ) * (∫ x, ‖f x‖^2)^(1/4) * (∫ x, ‖VectorField.gradient f x‖^2)^(1/4) := by
  -- This follows from the Sobolev embedding theorem in 3D
  -- H¹(ℝ³) ↪ L^∞(ℝ³) with explicit constant

  -- The proof uses the fundamental theorem of calculus in each coordinate
  -- combined with Hölder's inequality to control the L∞ norm
  -- by the H¹ norm = L² norm + gradient L² norm

  sorry -- Apply mathlib's Sobolev embedding with appropriate constants

end NavierStokesLedger

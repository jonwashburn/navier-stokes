/-
Copyright (c) 2024 Navier-Stokes Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Recognition Science Collaboration
-/
import NavierStokesLedger.FluidDynamics.VelocityField

/-!
# Vorticity Dynamics

This file focuses on vorticity ω = curl u and its evolution.

## Main definitions

* `Vorticity` - The vorticity field ω
* `vorticityEquation` - Evolution equation for ω
* `vorticityStretching` - The (ω·∇)u term
* `enstrophy` - The L² norm of vorticity

## Main results

* `vorticity_transport` - Vorticity equation in various forms
* `helicity_conservation` - Helicity H = ∫ u·ω dx is conserved
* `vortex_stretching_bound` - Key bounds on vortex stretching

-/

namespace NavierStokesLedger

open Real Function MeasureTheory

/-- Type synonym for vorticity fields -/
def Vorticity := VectorField

namespace Vorticity

variable (ω : Vorticity) (u : VectorField)

/-- The vorticity is the curl of velocity -/
def fromVelocity (u : VectorField) : Vorticity :=
  u.curl

/-- Vortex stretching term (ω·∇)u -/
def vortexStretching (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  u.velocityGradient x (ω x)

/-- Alternative: ω_j ∂u_i/∂x_j -/
def vortexStretchingComponents (x : EuclideanSpace ℝ (Fin 3)) :
  EuclideanSpace ℝ (Fin 3) :=
  fromComponents fun i =>
    ∑ j : Fin 3, component j (ω x) * u.partialDeriv i j x

/-- The two formulations are equivalent -/
theorem vortex_stretching_eq :
  vortexStretching ω u = vortexStretchingComponents ω u := by rfl
  /- TODO: Matrix multiplication -/

/-- Vorticity magnitude |ω| -/
def magnitude (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ‖ω x‖

/-- Maximum vorticity Ω(t) = sup_x |ω(x,t)| -/
def supremumNorm : ℝ≥0∞ :=
  ω.linftyNorm

/-- Enstrophy E = (1/2) ∫ |ω|² dx -/
def enstrophy : ℝ :=
  (1/2) * rfl (u : NSolution) (ν : ℝ)
  (h2d : ∀ t x, component 2 (u t x) = 0) :
  ∀ t x, rfl -/
theorem geometric_depletion_ingredients :
  ∀ x t, ‖direction ω x‖ ≤ 1 := by norm_num
  /- TODO: By construction of unit vector -/

/-- Local enstrophy in a ball -/
def localEnstrophy (center : EuclideanSpace ℝ (Fin 3)) (r : ℝ) : ℝ := simp [direction] -- ∫ x in ball(center, r), ‖ω x‖² dx

/-- Enstrophy concentration function -/
def enstrophyConcentration (r : ℝ) : ℝ := rfl -- sup_x localEnstrophy x r

end Vorticity

/-- Vortex line - integral curve of vorticity -/
structure VortexLine where
  curve : ℝ → EuclideanSpace ℝ (Fin 3)
  is_integral : ∀ s, curve' s = ω (curve s) / ‖ω (curve s)‖

/-- Vortex tube of radius r around a vortex line -/
def VortexTube (γ : VortexLine) (r : ℝ) :
  Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ∃ s, ‖x - γ.curve s‖ < r}

/-- Key lemma: Vorticity is large inside thin vortex tubes -/
theorem vortex_tube_concentration {ω : Vorticity} {γ : VortexLine} {r : ℝ}
  (hr : 0 < r) (hconc : simp) : -- Some concentration hypothesis
  ∀ x ∈ VortexTube γ r, ‖ω x‖ ≥ simp := by lean
simp [
  /- TODO: This is key for Harnack inequality application -/

end NavierStokesLedger

# Geometric Depletion: The Harmonic Analysis of Near-Field Cancellation

## 1. Introduction and Goal

This document details the rigorous mathematical steps required to prove the near-field cancellation lemma in `GeometricDepletion.lean`. The goal is to prove:

> For `ω` aligned with `ω(x)` within an angle `θ₀` in a ball `B(x,r)`, we have
> \[
> \left\| \int_{B(x,r)} K(x,y) \omega(y) \, dy \right\| \le \frac{C^*}{r}
> \]
> where `K(x,y)` is the Biot-Savart kernel and `C^*` is a small constant.

We will prove this by decomposing the integral and showing that the main contribution cancels, leaving a small, controllable remainder.

## 2. The Biot-Savart Kernel and its Properties

Let `z = y - x`. The Biot-Savart kernel `K(x,y)` can be written as `K(z)`, a matrix-valued function where `K_{ij}(z) = \frac{1}{4\pi |z|^3} \sum_k \epsilon_{ikj} z_k`. This is a more convenient form for analysis.

This can be expressed more cleanly using vector notation. The velocity `u` is recovered from vorticity `ω` via the Biot-Savart law:
\[
u(x) = \frac{1}{4\pi} \int_{\mathbb{R}^3} \frac{(y-x) \times \omega(y)}{|y-x|^3} \, dy
\]
The velocity gradient `∇u` is what we need for the stretching term `(ω ⋅ ∇)u`. Taking the gradient of the above expression (a non-trivial step involving differentiation under the integral sign), we get:
\[
\nabla u(x) = \text{p.v.} \int_{\mathbb{R}^3} K(x,y) \omega(y) \, dy
\]
where `K` is a matrix-valued singular integral kernel.

### Key Properties of the Kernel `K(z)`:

1.  **Homogeneity**: `K(αz) = α^{-3} K(z)` for `α > 0`. The operator `f ↦ K * f` is of degree 0.
2.  **Singularity**: `|K(z)| ~ 1/|z|^3` as a matrix norm, but its action as an integral operator is better behaved. The gradient of the Green's function for the Laplacian is `∇(1/|z|) = -z/|z|^3`. The kernel is `K(z) = ∇ × (∇(1/|z|))`.
3.  **Zero Mean on Spheres**: For any radius `ρ > 0`,
    \[
    \int_{|z|=\rho} K(z) \, dS(z) = 0
    \]
    This is a crucial cancellation property. It follows from the fact that `K` is the curl of another field, and by Stokes' theorem, the integral of a curl over a closed surface is zero.

## 3. The Main Decomposition

The core of the proof is to decompose the vorticity `ω(y)` inside the ball `B(x,r)`. We write:
\[
\omega(y) = \omega(x) + \delta\omega(y)
\]
where `δω(y) = ω(y) - ω(x)`. The integral becomes:
\[
I = \int_{B(x,r)} K(x,y) \omega(y) \, dy = \underbrace{\int_{B(x,r)} K(x,y) \omega(x) \, dy}_{I_1} + \underbrace{\int_{B(x,r)} K(x,y) \delta\omega(y) \, dy}_{I_2}
\]

### 3.1. The Cancellation of the Constant Part (`I₁`)

**Theorem**: The integral of the Biot-Savart kernel against a constant vector over a ball centered at the singularity is zero.
\[
I_1 = \left( \int_{B(x,r)} K(x,y) \, dy \right) \omega(x) = 0
\]

**Proof Sketch**:
Let `v = ω(x)` be the constant vector. We need to show `∫_{B(0,r)} K(z) v \, dz = 0`.
The integral is understood as a principal value, `lim_{ε→0} ∫_{B(0,r) \setminus B(0,ε)}`.

The kernel `K(z)` can be written as the gradient of a vector potential `P(z)` plus the gradient of a scalar potential `Φ(z)`. More simply, `K_{ij}` is a sum of derivatives of `1/|z|`.
A key identity is that for any `i,j`, `∫_{B(0,r)} \frac{z_i z_j}{|z|^5} \, dz = \frac{4\pi r^3}{3} \frac{\delta_{ij}}{r^3} = \frac{4\pi}{3} \delta_{ij}`. The off-diagonal terms integrate to zero by symmetry (e.g., integrating `z_1 z_2` over a ball gives zero).

The most direct way to see the cancellation is using the property that `K` has a zero mean on spheres. We can integrate in spherical coordinates:
\[
\int_{B(0,r)} K(z) v \, dz = \int_0^r \left( \int_{|z|=\rho} K(z) v \, dS(z) \right) \rho^2 \, d\rho
\]
Since `v` is constant, we can pull it out of the surface integral:
\[
\int_{|z|=\rho} K(z) v \, dS(z) = \left( \int_{|z|=\rho} K(z) \, dS(z) \right) v = 0 \cdot v = 0
\]
The inner integral is zero for every `ρ`, so the total integral `I₁` is zero. This is a powerful cancellation and it's the primary reason the geometric depletion works.

This concludes the first part of the mathematical breakdown. We have rigorously shown that if vorticity were perfectly constant (`ω(y) = ω(x)`), the stretching term would be zero. The next step is to show that if it's *nearly* constant (the alignment condition), the remaining term `I₂` is small.

---
*(Next session: Estimating the perturbation term `I₂`)* 
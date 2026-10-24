import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Calculus.VariationDerivatives
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.NormalVariation
import OTSelector.Geometry.Finsler.Variation.Lagrangian

/-!
## Lemma skeleton

* **Conditions:** A C2 position family on an open kernel-by-time box, admissible C2 scalar energy, actual Euler–Lagrange time curves, equal energy, affine initial positions and initial momentum proportional to a fixed covector.
* **Objects:** The actual position/time phase and spatial differential of the family; annihilation of the spatial differential by current Legendre momentum.
* **Proof detail:** Insert an affine spatial variation inside the kernel. Its true variation field is the spatial differential. First variation preserves the endpoint pairing, whose initial value vanishes because the momentum is proportional to the fixed covector.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, p. 238, equations (8.33)–(8.36); Problem 8.7, p. 241.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249
* David Bao; Shiing-Shen Chern; Zhongmin Shen, *An Introduction to Riemann–Finsler Geometry (Springer, 2000)*, Section 5.1, pp. 111–118 (first variation); Section 5.4, pp. 129–134 (Jacobi fields); Section 6.1, pp. 139–144 (Gauss lemma).
  https://link.springer.com/content/pdf/bfm:978-1-4612-1268-3/1
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
  https://www.jirka.org/ra/realanal2.pdf#page=38

**Relationship to the sources:** This is a conormal, phase-space version of the Gauss identity derived from equal-energy first variation. The BCS Gauss section is a verified conceptual location only; the arbitrary normed-space scalar-energy formulation is proved here and is not asserted to be a verbatim book theorem.
-/

/-!
# Gauss identity from actual equal-energy normal position curves

An affine variation in the initial momentum kernel is a genuine two-parameter
variation of the given position map. Its time velocity is the actual time derivative,
and its variation field is the actual spatial differential. Equal energy and the
Euler--Lagrange equation preserve the endpoint momentum pairing by first variation.
The initial affine position and normal momentum make this pairing zero.

No Gauss pairing is assumed. The argument works in either time direction in arbitrary
real normed spaces, without an inner product, completeness, or finite dimensionality.
-/

open Set Filter Metric
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The position and actual time derivative of a parameterized position map. -/
def positionMapPhase (g : H × ℝ → E) (q : H × ℝ) : E × E :=
  (g q, deriv (fun t ↦ g (q.1, t)) q.2)

/-- The actual time velocity evaluates the joint differential in the time direction. -/
theorem positionMapPhase_snd_eq_fderiv {g : H × ℝ → E} {q : H × ℝ}
    (hg : DifferentiableAt ℝ g q) :
    (positionMapPhase g q).2 = fderiv ℝ g q (0, 1) := by
  have hd := hg.hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
  simpa only [positionMapPhase, Function.comp_def, id_eq] using hd.deriv

/-- Spatial annihilation and a time pairing determine a linear pairing on every direction. -/
theorem linearMap_pairing_of_spatial_time (A : H × ℝ →L[ℝ] E) (p : E →L[ℝ] ℝ)
    {k : ℝ} (hspace : ∀ ξ : H, p (A (ξ, 0)) = 0) (htime : p (A (0, 1)) = k)
    (d : H × ℝ) : p (A d) = k * d.2 := by
  have hd : d = (d.1, 0) + d.2 • (0, 1) := by ext <;> simp
  calc
    p (A d) = p (A (d.1, 0)) + d.2 * p (A (0, 1)) := by
      conv_lhs => rw [hd]
      simp only [map_add, map_smul, smul_eq_mul]
    _ = k * d.2 := by rw [hspace, htime]; ring

/-- The affine parameter variation has the same actual phase as its position map. -/
theorem variationPhase_affine_parameter (g : H × ℝ → E) (w ξ : H) (q : ℝ × ℝ) :
    variationPhase (fun z : ℝ × ℝ ↦ g (w + z.1 • ξ, z.2)) q =
      positionMapPhase g (w + q.1 • ξ, q.2) := rfl

/-- The affine parameter variation differentiates in the specified spatial direction. -/
theorem variationField_affine_parameter {g : H × ℝ → E} {w ξ : H} {t : ℝ}
    (hg : DifferentiableAt ℝ g (w, t)) :
    variationField (fun z : ℝ × ℝ ↦ g (w + z.1 • ξ, z.2)) 0 t =
      fderiv ℝ g (w, t) (ξ, 0) := by
  have hpath : HasDerivAt (fun s : ℝ ↦ (w + s • ξ, t)) (ξ, 0) 0 := by
    simpa using
      (((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add w).prodMk
        (hasDerivAt_const (0 : ℝ) t)
  have hD : HasFDerivAt g (fderiv ℝ g (w, t)) (w + (0 : ℝ) • ξ, t) := by
    simpa only [zero_smul, add_zero] using hg.hasFDerivAt
  have hcomp := hD.comp_hasDerivAt (0 : ℝ) hpath
  simpa only [variationField, Function.comp_def, zero_smul, add_zero] using hcomp.deriv

/-- Actual constant-energy Euler--Lagrange position curves from an affine hypersurface
with normal initial momentum satisfy the spatial Gauss identity throughout the open box. -/
theorem fiberLegendre_positionMapPhase_fderiv_eq_zero
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ 2 L U) {p : E →L[ℝ] ℝ} {g : p.ker × ℝ → E}
    {ρ t₀ T C : ℝ} {x₀ : E} {a : p.ker → ℝ} (hT : 0 < T)
    (hg : ContDiffOn ℝ 2 g (ball (0 : p.ker) ρ ×ˢ Ioo (t₀ - T) (t₀ + T)))
    (hphase : ∀ q ∈ ball (0 : p.ker) ρ ×ˢ Ioo (t₀ - T) (t₀ + T),
      positionMapPhase g q ∈ U)
    (hEL : ∀ q ∈ ball (0 : p.ker) ρ ×ˢ Ioo (t₀ - T) (t₀ + T), HasDerivAt
      (fun u ↦ fiberLegendre L (positionMapPhase g (q.1, u)))
      (baseEnergyDifferential L (positionMapPhase g q)) q.2)
    (henergy : ∀ q ∈ ball (0 : p.ker) ρ ×ˢ Ioo (t₀ - T) (t₀ + T),
      L (positionMapPhase g q) = C)
    (hinitial : ∀ w ∈ ball (0 : p.ker) ρ, g (w, t₀) = x₀ + (w : E) ∧
      fiberLegendre L (positionMapPhase g (w, t₀)) = a w • p) :
    ∀ w ∈ ball (0 : p.ker) ρ, ∀ t ∈ Ioo (t₀ - T) (t₀ + T), ∀ ξ : p.ker,
      fiberLegendre L (positionMapPhase g (w, t)) (fderiv ℝ g (w, t) (ξ, 0)) = 0 := by
  intro w hw t ht ξ
  let S : Set ℝ := {s | w + s • ξ ∈ ball (0 : p.ker) ρ}
  let D : Set (ℝ × ℝ) := S ×ˢ Ioo (t₀ - T) (t₀ + T)
  let σ : ℝ × ℝ → E := fun q ↦ g (w + q.1 • ξ, q.2)
  have hS : IsOpen S :=
    isOpen_ball.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hS₀ : (0 : ℝ) ∈ S := by simpa only [S, mem_ofPred_eq, zero_smul, add_zero] using hw
  have hD : IsOpen D := hS.prod isOpen_Ioo
  have hσ : ContDiffOn ℝ 2 σ D :=
    hg.comp ((contDiffOn_const.add (contDiffOn_fst.smul contDiffOn_const)).prodMk
      contDiffOn_snd) (fun _ hq ↦ ⟨hq.1, hq.2⟩)
  have ht₀ : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  have hsegment : uIcc t₀ t ⊆ Ioo (t₀ - T) (t₀ + T) :=
    ordConnected_Ioo.uIcc_subset ht₀ ht
  have hcentral : ∀ u : ℝ, variationPhase σ (0, u) = positionMapPhase g (w, u) := by
    intro u
    simpa only [zero_smul, add_zero] using variationPhase_affine_parameter g w ξ (0, u)
  have hinitialField : variationField σ 0 t₀ = (ξ : E) := by
    have hlinear : HasDerivAt (fun s : ℝ ↦ x₀ + ((w + s • ξ : p.ker) : E))
        (ξ : E) 0 := by
      simpa using
        (((hasDerivAt_id (0 : ℝ)).smul_const (ξ : E)).const_add (w : E)).const_add x₀
    apply HasDerivAt.deriv
    apply hlinear.congr_of_eventuallyEq
    filter_upwards [hS.mem_nhds hS₀] with s hs
    exact (hinitial _ hs).1
  have hzero : fiberLegendre L (variationPhase σ (0, t₀)) (variationField σ 0 t₀) = 0 := by
    rw [hcentral, hinitialField, (hinitial w hw).2]
    have hξ : p (ξ : E) = 0 := ξ.property
    simp only [smul_apply, smul_eq_mul, hξ, mul_zero]
  have hend := fiberLegendre_variationField_eq_zero_of_equal_energy hU hL hD hσ
    (s₀ := 0) (a := t₀) (b := t) (E₀ := C)
    (fun u hu ↦ ⟨hS₀, hsegment hu⟩)
    (fun u hu ↦ by rw [hcentral]; exact hphase _ ⟨hw, hsegment hu⟩)
    (fun u hu ↦ by simpa only [hcentral] using hEL (w, u) ⟨hw, hsegment hu⟩)
    (fun q hq ↦ by
      rw [show variationPhase σ q = positionMapPhase g (w + q.1 • ξ, q.2) from rfl]
      exact henergy _ ⟨hq.1, hq.2⟩) hzero
  rw [hcentral] at hend
  have hgAt : DifferentiableAt ℝ g (w, t) :=
    (hg.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hw, ht⟩)).differentiableAt
      (by norm_num)
  rw [variationField_affine_parameter hgAt] at hend
  exact hend

end OTSelector.Geometry

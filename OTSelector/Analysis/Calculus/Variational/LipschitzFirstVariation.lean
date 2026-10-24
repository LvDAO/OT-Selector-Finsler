import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import OTSelector.Analysis.Calculus.CompactAEDifferentiationIntegral
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.LipschitzLagrangianFirstVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.LipschitzLagrangianFirstVariation`; the selected original proof blocks follow. -/
section

/-!
Conditions: The center path is Lipschitz, its phase is almost everywhere in a compact admissible set, and the stated differentiability and domination bounds hold for a C1 perturbation.

Objects: First variation of the actual integral action around that Lipschitz center.

Proof detail: Obtain almost-everywhere phase bounds, differentiate the integrand along the perturbation and pass the derivative through the integral with the compact domination.

Sources: Gerald Teschl, Section 8.3, p. 238, equations (8.33)–(8.36); Problem 8.7, p. 241 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249); Jiří Lebl, Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters) (https://www.jirka.org/ra/html/sec_diffunderint.html); D. H. Fremlin, Section 262P, p. 17 (measurability of derivative); Theorem 262Q, pp. 18–20 (Rademacher) (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=17).
Relation: An extension of the classical smooth-path first-variation computation to the explicit almost-everywhere setting; no C1 center is assumed.
-/

/-!
# Raw first variation at a Lipschitz Lagrangian curve

A Lipschitz center with almost-everywhere compact admissible phase admits the
unintegrated first variation along every C1 additive perturbation. The center is not
assumed C1 or C2. All measurability, integrability and uniform bounds are derived.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

noncomputable section

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A C1 perturbation has a Lipschitz constant on every closed bounded time interval. -/
theorem exists_lipschitzOnWith_Icc_of_contDiff {η : ℝ → E}
    (hη : ContDiff ℝ 1 η) (a b : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K η (Icc a b) :=
  hη.contDiffOn.exists_lipschitzOnWith (by simp) (convex_Icc a b) isCompact_Icc

variable [FiniteDimensional ℝ E]

/-- The actual raw Lagrangian action has its usual first variation at a Lipschitz center
whose phase is almost everywhere in a compact subset of the C1 domain. -/
theorem hasDerivAt_intervalIntegral_lagrangian_add_of_compact_ae
    {L : E × E → ℝ} {U P : Set (E × E)}
    (hU : IsOpen U) (hL : ContDiffOn ℝ 1 L U) (hP : IsCompact P) (hPU : P ⊆ U)
    {a b : ℝ} {x η : ℝ → E} {Kx : ℝ≥0} (hab : a ≤ b)
    (hx : LipschitzOnWith Kx x (Icc a b))
    (hphase : ∀ᵐ t ∂volume.restrict (Ioo a b), (x t, deriv x t) ∈ P)
    (hη : ContDiff ℝ 1 η) :
    HasDerivAt
      (fun s : ℝ ↦ ∫ t in a..b, L (x t + s • η t, deriv x t + s • deriv η t))
      (∫ t in a..b, baseEnergyDifferential L (x t, deriv x t) (η t) +
        fiberLegendre L (x t, deriv x t) (deriv η t)) 0 := by
  let z : ℝ → E × E := fun t ↦ (x t, deriv x t)
  let w : ℝ → E × E := fun t ↦ (η t, deriv η t)
  have hz : AEStronglyMeasurable z (volume.restrict (Ioo a b)) :=
    ((hx.continuousOn.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo).prodMk
      (aestronglyMeasurable_deriv x _)
  have hwcont : Continuous w := hη.continuous.prodMk hη.continuous_deriv_one
  have hw : AEStronglyMeasurable w (volume.restrict (Ioo a b)) :=
    hwcont.aestronglyMeasurable
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hwcont.continuousOn
  let C' : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hwC : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖w t‖ ≤ (C' : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hC t (Ioo_subset_Icc_self ht)).trans (le_max_left _ _)
  have h := (hasDerivAt_integral_add_smul_of_compact_ae hU hL hP hPU hz hphase hw hwC).2
  have heq : (∫ t in Ioo a b, fderiv ℝ L (z t) (w t)) =
      ∫ t in Ioo a b, baseEnergyDifferential L (x t, deriv x t) (η t) +
        fiberLegendre L (x t, deriv x t) (deriv η t) := by
    apply integral_congr_ae
    filter_upwards [hphase] with t ht
    exact fderiv_energy_split
      ((hL.contDiffAt (hU.mem_nhds (hPU ht))).differentiableAt_one) (η t) (deriv η t)
  rw [heq] at h
  simpa only [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    z, w, Prod.smul_mk, Prod.mk_add_mk] using h

end OTSelector.Geometry

end
end

import OTSelector.Analysis.Calculus.Variational.EndpointHessianCalculus
import OTSelector.Analysis.Calculus.Variational.EndpointJacobiCompliance
import OTSelector.LinearAlgebra.Dual.CovectorKernel
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.KernelEndpointCompliance.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.KernelEndpointCompliance`; the selected original proof blocks follow. -/
section

/-!
Conditions: A nonzero covector, its transverse kernel/dual lift, a positive symmetric operator and the stated radial identity.

Objects: Compressed integrated compliance and agreement of its inverse with the full inverse on the kernel.

Proof detail: Commute continuous linear lift/projection through the integral, prove strict positivity on the kernel, then verify the inverse identity directly from the radial relation.

Sources: Jiří Lebl, Section 5.3.1, Theorem 5.3.1, pp. 200–201 (https://www.jirka.org/ra/realanal.pdf#page=200); Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Explicit kernel-compression corollary; it does not assume an unproved commutation of restriction and inversion.
-/

/-!
# Kernel compression of the actual endpoint compliance

The fixed covector-kernel compression commutes with the operator integral. The actual
radial pairing identifies the inverse full compliance, on kernel vectors, with the
inverse compressed integral. No commutation of restriction and inversion is assumed.
-/

open Set MeasureTheory
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equality of the actual responses on the closed interval gives equality of their integrals. -/
theorem endpointCompliance_congr_on
    {C D : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ} (hab : a ≤ b)
    (hCD : EqOn C D (Icc a b)) : endpointCompliance C a b = endpointCompliance D a b := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact hCD (by simpa only [uIcc_of_le hab] using ht)

/-- A covector vanishing on the radial vector is recovered by extending its restriction. -/
theorem covectorKernelDualLift_restrict_of_radial_zero
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) (q : E →L[ℝ] ℝ) (hq : q v = 0) :
    covectorKernelDualLift p v hv (q.comp p.ker.subtypeL) = q := by
  ext x
  change q (covectorKernelProjection p v hv x : E) = q x
  rw [covectorKernelProjection_coe]
  simp [hq]

/-- Fixed kernel compression preserves continuity of an operator-valued response. -/
theorem continuousOn_covectorKernelCompression
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {I : Set ℝ} (hC : ContinuousOn C I) :
    ContinuousOn (fun t ↦ covectorKernelCompression p v hv (C t)) I :=
  continuousOn_const.clm_comp (hC.clm_comp continuousOn_const)

variable [FiniteDimensional ℝ E]

/-- Kernel compression and the actual operator integral commute. -/
theorem endpointCompliance_kernelCompression_eq
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a ≤ b) (hC : ContinuousOn C (Icc a b)) :
    endpointCompliance (fun t ↦ covectorKernelCompression p v hv (C t)) a b =
      covectorKernelCompression p v hv (endpointCompliance C a b) := by
  apply ContinuousLinearMap.ext
  intro η
  rw [endpointCompliance_apply hab (continuousOn_covectorKernelCompression p v hv hC)]
  change (∫ t in a..b, covectorKernelProjection p v hv
    (C t (covectorKernelDualLift p v hv η))) =
      covectorKernelProjection p v hv
        (endpointCompliance C a b (covectorKernelDualLift p v hv η))
  rw [endpointCompliance_apply hab hC,
    (covectorKernelProjection p v hv).intervalIntegral_comp_comm
      ((hC.clm_apply continuousOn_const).intervalIntegrable_of_Icc hab)]

/-- Positivity constructs an inverse for the compressed integral as well. -/
theorem endpointCompliance_kernelCompression_isInvertible
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a < b) (hC : ContinuousOn C (Icc a b))
    (hpos : ∀ t ∈ Icc a b, ∀ q : E →L[ℝ] ℝ, q ≠ 0 → 0 < q (C t q)) :
    (endpointCompliance (fun t ↦ covectorKernelCompression p v hv (C t)) a b).IsInvertible :=
  endpointCompliance_isInvertible hab (continuousOn_covectorKernelCompression p v hv hC)
    (fun t ht _ hη ↦ covectorKernelCompression_pos p v hv (hpos t ht) hη)

/-- The inverse full integral, paired on kernel vectors, equals the inverse of the
compressed integral. Radial compatibility and positivity are used to prove this identity. -/
theorem endpointCompliance_inverse_on_kernel
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a < b) (hC : ContinuousOn C (Icc a b))
    (hpos : ∀ t ∈ Icc a b, ∀ q : E →L[ℝ] ℝ, q ≠ 0 → 0 < q (C t q))
    (hrad : ∀ t ∈ Icc a b, ∀ q : E →L[ℝ] ℝ, p (C t q) = q v)
    (u w : p.ker) :
    (endpointCompliance C a b).inverse (u : E) (w : E) =
      (endpointCompliance (fun t ↦ covectorKernelCompression p v hv (C t)) a b).inverse u w := by
  let S := endpointCompliance C a b
  let SK := endpointCompliance (fun t ↦ covectorKernelCompression p v hv (C t)) a b
  have hS : S.IsInvertible := endpointCompliance_isInvertible hab hC hpos
  have hSK : SK.IsInvertible :=
    endpointCompliance_kernelCompression_isInvertible p v hv hab hC hpos
  let q := S.inverse (u : E)
  have hq : q v = 0 := by
    have h := endpointCompliance_inverse_radial_pairing hab hC p v hrad hS (u : E)
    simpa only [show p (u : E) = 0 from u.property, zero_div] using h
  have hlift := covectorKernelDualLift_restrict_of_radial_zero p v hv q hq
  have hSKq : SK (q.comp p.ker.subtypeL) = u := by
    dsimp only [SK]
    rw [endpointCompliance_kernelCompression_eq p v hv hab.le hC]
    change covectorKernelProjection p v hv (S (covectorKernelDualLift p v hv
      (q.comp p.ker.subtypeL))) = u
    rw [hlift, show S q = (u : E) from hS.self_apply_inverse (u : E),
      covectorKernelProjection_subtype]
  have hqK : q.comp p.ker.subtypeL = SK.inverse u := by
    rw [← hSKq, hSK.inverse_apply_self]
  exact congrArg (fun η : p.ker →L[ℝ] ℝ ↦ η w) hqK

end OTSelector.Geometry

end
end

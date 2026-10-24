import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.EndpointJacobiCompliance.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.EndpointJacobiCompliance`; the selected original proof blocks follow. -/
section

/-!
Conditions: A continuous symmetric positive response from covectors to vectors on a nontrivial compact interval, with the stated Jacobi equations.

Objects: Integrated endpoint compliance, invertibility and positivity of its inverse, and the constant-momentum endpoint formula.

Proof detail: Integrate the response, pair with a nonzero covector to prove strict positivity, use finite-dimensional injectivity and integrate J′=CP with P′=0.

Sources: Jiří Lebl, Section 5.3.1, Theorem 5.3.1, pp. 200–201 (https://www.jirka.org/ra/realanal.pdf#page=200); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48).
Relation: A locally proved positive-operator integral and boundary-value corollary, rather than a curvature-specific Jacobi theorem.
-/

/-!
# The integral compliance of an endpoint Jacobi equation

The actual operator integral of a continuous positive momentum-to-velocity response
is positive and invertible in finite dimension. Constant momentum and its integrated
position equation identify momentum from the two endpoint variations. Symmetry is
preserved by both integration and inversion under the canonical dual pairing.
-/

open Set MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The operator obtained by integrating the actual momentum-to-velocity response. -/
def endpointCompliance (C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E) (a b : ℝ) :
    (E →L[ℝ] ℝ) →L[ℝ] E := ∫ t in a..b, C t

omit [FiniteDimensional ℝ E] in
/-- Evaluation commutes with the actual operator integral. -/
theorem endpointCompliance_apply {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a ≤ b) (hC : ContinuousOn C (Icc a b)) (p : E →L[ℝ] ℝ) :
    endpointCompliance C a b p = ∫ t in a..b, C t p := by
  exact ContinuousLinearMap.intervalIntegral_apply
    (hC.intervalIntegrable_of_Icc hab) p

/-- The integral of a continuous strictly positive response is itself strictly positive. -/
theorem endpointCompliance_pos {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a < b) (hC : ContinuousOn C (Icc a b))
    (hpos : ∀ t ∈ Icc a b, ∀ p : E →L[ℝ] ℝ, p ≠ 0 → 0 < p (C t p))
    {p : E →L[ℝ] ℝ} (hp : p ≠ 0) : 0 < p (endpointCompliance C a b p) := by
  have hc : ContinuousOn (fun t ↦ C t p) (Icc a b) := hC.clm_apply continuousOn_const
  rw [endpointCompliance_apply hab.le hC,
    ← p.intervalIntegral_comp_comm (hc.intervalIntegrable_of_Icc hab.le)]
  exact intervalIntegral.integral_pos hab (p.continuous.comp_continuousOn hc)
    (fun t ht ↦ (hpos t (Ioc_subset_Icc_self ht) p hp).le)
    ⟨a, left_mem_Icc.mpr hab.le, hpos a (left_mem_Icc.mpr hab.le) p hp⟩

/-- Positivity and the equality of primal and dual dimensions give bijectivity. -/
theorem endpointCompliance_bijective {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a < b) (hC : ContinuousOn C (Icc a b))
    (hpos : ∀ t ∈ Icc a b, ∀ p : E →L[ℝ] ℝ, p ≠ 0 → 0 < p (C t p)) :
    Function.Bijective (endpointCompliance C a b) := by
  have hi : Function.Injective (endpointCompliance C a b) := by
    apply (injective_iff_map_eq_zero _).2
    intro p hp
    by_contra hne
    have h := endpointCompliance_pos hab hC hpos hne
    simp [hp] at h
  have hdim : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
    rw [← (LinearMap.toContinuousLinearMap :
      (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq]
    exact Subspace.dual_finrank_eq
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

/-- The actual integral, rather than an assumed inverse, defines a continuous linear equivalence. -/
def endpointComplianceEquiv {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a < b) (hC : ContinuousOn C (Icc a b))
    (hpos : ∀ t ∈ Icc a b, ∀ p : E →L[ℝ] ℝ, p ≠ 0 → 0 < p (C t p)) :
    (E →L[ℝ] ℝ) ≃L[ℝ] E :=
  (LinearEquiv.ofBijective (endpointCompliance C a b).toLinearMap
    (endpointCompliance_bijective hab hC hpos)).toContinuousLinearEquiv

/-- The constructed equivalence retains exactly the original integral operator. -/
@[simp] theorem endpointComplianceEquiv_toContinuousLinearMap
    {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a < b) (hC : ContinuousOn C (Icc a b))
    (hpos : ∀ t ∈ Icc a b, ∀ p : E →L[ℝ] ℝ, p ≠ 0 → 0 < p (C t p)) :
    (endpointComplianceEquiv hab hC hpos).toContinuousLinearMap = endpointCompliance C a b := rfl

/-- The actual integral operator is invertible without an invertibility premise. -/
theorem endpointCompliance_isInvertible {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a < b) (hC : ContinuousOn C (Icc a b))
    (hpos : ∀ t ∈ Icc a b, ∀ p : E →L[ℝ] ℝ, p ≠ 0 → 0 < p (C t p)) :
    (endpointCompliance C a b).IsInvertible := ⟨endpointComplianceEquiv hab hC hpos, rfl⟩

/-- Symmetry of the actual response passes through the operator integral. -/
theorem endpointCompliance_symm {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a ≤ b) (hC : ContinuousOn C (Icc a b))
    (hsym : ∀ t ∈ Icc a b, ∀ p q : E →L[ℝ] ℝ, p (C t q) = q (C t p))
    (p q : E →L[ℝ] ℝ) : p (endpointCompliance C a b q) = q (endpointCompliance C a b p) := by
  rw [endpointCompliance_apply hab hC, endpointCompliance_apply hab hC,
    ← p.intervalIntegral_comp_comm
      ((hC.clm_apply continuousOn_const).intervalIntegrable_of_Icc hab),
    ← q.intervalIntegral_comp_comm
      ((hC.clm_apply continuousOn_const).intervalIntegrable_of_Icc hab)]
  apply intervalIntegral.integral_congr
  intro t ht
  exact hsym t (by simpa only [uIcc_of_le hab] using ht) p q

/-- The inverse integral remains positive under the original vector-covector pairing. -/
theorem endpointCompliance_inverse_pos {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a < b) (hC : ContinuousOn C (Icc a b))
    (hpos : ∀ t ∈ Icc a b, ∀ p : E →L[ℝ] ℝ, p ≠ 0 → 0 < p (C t p))
    {v : E} (hv : v ≠ 0) : 0 < (endpointCompliance C a b).inverse v v := by
  let d := endpointComplianceEquiv hab hC hpos
  have hinv : (endpointCompliance C a b).inverse = d.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv d
  rw [hinv]
  have hp : d.symm v ≠ 0 := d.symm.map_eq_zero_iff.not.mpr hv
  have h := endpointCompliance_pos hab hC hpos hp
  change 0 < (d.symm v) (d (d.symm v)) at h
  simpa only [d.apply_symm_apply] using! h

/-- Symmetry of the response also gives symmetry of the actual inverse integral. -/
theorem endpointCompliance_inverse_symm {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {a b : ℝ}
    (hab : a < b) (hC : ContinuousOn C (Icc a b))
    (hpos : ∀ t ∈ Icc a b, ∀ p : E →L[ℝ] ℝ, p ≠ 0 → 0 < p (C t p))
    (hsym : ∀ t ∈ Icc a b, ∀ p q : E →L[ℝ] ℝ, p (C t q) = q (C t p))
    (u v : E) : (endpointCompliance C a b).inverse u v =
      (endpointCompliance C a b).inverse v u := by
  let d := endpointComplianceEquiv hab hC hpos
  have hinv : (endpointCompliance C a b).inverse = d.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv d
  rw [hinv]
  have h := endpointCompliance_symm hab.le hC hsym (d.symm u) (d.symm v)
  change (d.symm u) (d (d.symm v)) = (d.symm v) (d (d.symm u)) at h
  simpa only [d.apply_symm_apply] using! h

/-- Solving the actual differential equations recovers momentum from the endpoint displacement. -/
theorem momentum_eq_endpointCompliance_inverse
    {J : ℝ → E} {P : ℝ → (E →L[ℝ] ℝ)} {C : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E}
    {a b : ℝ} (hab : a < b) (hC : ContinuousOn C (Icc a b))
    (hpos : ∀ t ∈ Icc a b, ∀ p : E →L[ℝ] ℝ, p ≠ 0 → 0 < p (C t p))
    (hJ : ∀ t ∈ Icc a b, HasDerivAt J (C t (P t)) t)
    (hP : ∀ t ∈ Icc a b, HasDerivAt P 0 t) :
    ∀ t ∈ Icc a b, P t = (endpointCompliance C a b).inverse (J b - J a) := by
  have hPa (t : ℝ) (ht : t ∈ Icc a b) : P t = P a := by
    apply Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (convex_Icc a b)
      (fun s hs ↦ (hP s hs).differentiableAt.differentiableWithinAt) ?_ ht
      (left_mem_Icc.mpr hab.le)
    intro s hs
    simpa using ((hP s hs).hasFDerivAt.hasFDerivWithinAt.fderivWithin
      ((uniqueDiffOn_Icc hab) s hs))
  have hS : endpointCompliance C a b (P a) = J b - J a := by
    rw [endpointCompliance_apply hab.le hC]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using ht
      simpa only [hPa t ht'] using hJ t ht'
    · exact (hC.clm_apply continuousOn_const).intervalIntegrable_of_Icc hab.le
  intro t ht
  rw [hPa t ht, ← hS]
  let d := endpointComplianceEquiv hab hC hpos
  rw [show (endpointCompliance C a b).inverse = d.symm.toContinuousLinearMap from
    ContinuousLinearMap.inverse_equiv d]
  exact (d.symm_apply_apply (P a)).symm

end OTSelector.Geometry

end
end

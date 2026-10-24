import Mathlib.Analysis.Calculus.ContDiff.Operations
import OTSelector.Analysis.Calculus.Variational.EndpointJacobiCompliance
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.EndpointComplianceUniform.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.EndpointComplianceUniform`; the selected original proof blocks follow. -/
section

/-!
Conditions: A continuous strictly positive symmetric response and a compact family of ordered nontrivial endpoint pairs.

Objects: Jointly continuous inverse compliance and uniform two-sided quadratic bounds.

Proof detail: Continuity of parameter interval integrals gives compliance continuity; positivity gives invertibility, then compactness bounds the form and inverse.

Sources: Jiří Lebl, Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters) (https://www.jirka.org/ra/html/sec_diffunderint.html); Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Positive-operator integral/compactness corollary, including empty and zero-dimensional cases under the actual conventions.
-/

/-!
# Uniform inverse compliance on compact ordered endpoint sets

Continuity of the actual response gives joint continuity of its endpoint integral.
Positivity makes the inverse continuous on ordered pairs. Compactness of the endpoint
set and the unit sphere then yields two-sided quadratic bounds, including empty sets
and zero-dimensional spaces.
-/

open Set Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

/-- The actual inverse integral is continuous and uniformly positive definite on a
compact set of strictly ordered endpoints in one fixed interval. -/
theorem endpointCompliance_inverse_continuous_uniform_bounds
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {C : ℝ → (V →L[ℝ] ℝ) →L[ℝ] V} {l r : ℝ} (hlr : l ≤ r)
    (hC : ContinuousOn C (Icc l r))
    (hpos : ∀ t ∈ Icc l r, ∀ p : V →L[ℝ] ℝ, p ≠ 0 → 0 < p (C t p))
    {T : Set (ℝ × ℝ)} (hT : IsCompact T)
    (hord : ∀ q ∈ T, l ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ r) :
    ContinuousOn (fun q ↦ (endpointCompliance C q.1 q.2).inverse) T ∧
      ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧
        ∀ q ∈ T, ∀ v : V,
          c₀ * ‖v‖ ^ 2 ≤ (endpointCompliance C q.1 q.2).inverse v v ∧
          (endpointCompliance C q.1 q.2).inverse v v ≤ C₀ * ‖v‖ ^ 2 := by
  let : NormedAddCommGroup ((V →L[ℝ] ℝ) →L[ℝ] V) := inferInstance
  let P : ℝ → (V →L[ℝ] ℝ) →L[ℝ] V := fun t ↦ ∫ s in l..t, C s
  let H : (ℝ × ℝ) → V →L[ℝ] (V →L[ℝ] ℝ) :=
    fun q ↦ (endpointCompliance C q.1 q.2).inverse
  have hP : ContinuousOn P (Icc l r) := by
    simpa only [P, uIcc_of_le hlr] using
      (intervalIntegral.continuousOn_primitive_interval'
        (hC.intervalIntegrable_of_Icc (μ := volume) hlr) (a := l) left_mem_uIcc)
  have hfst : MapsTo Prod.fst T (Icc l r) := by
    intro q hq
    exact ⟨(hord q hq).1, (hord q hq).2.1.le.trans (hord q hq).2.2⟩
  have hsnd : MapsTo Prod.snd T (Icc l r) := by
    intro q hq
    exact ⟨(hord q hq).1.trans (hord q hq).2.1.le, (hord q hq).2.2⟩
  have hsub (q : ℝ × ℝ) (hq : q ∈ T) : Icc q.1 q.2 ⊆ Icc l r :=
    Icc_subset_Icc (hord q hq).1 (hord q hq).2.2
  have hIntegral : ContinuousOn (fun q ↦ endpointCompliance C q.1 q.2) T := by
    have hdifference : ContinuousOn (fun q : ℝ × ℝ ↦ P q.2 - P q.1) T :=
      (hP.comp continuousOn_snd hsnd).sub (hP.comp continuousOn_fst hfst)
    apply hdifference.congr
    intro q hq
    have ha : IntervalIntegrable C volume l q.1 :=
      (hC.mono (Icc_subset_Icc le_rfl (hfst hq).2)).intervalIntegrable_of_Icc
        (μ := volume) (hfst hq).1
    have hb : IntervalIntegrable C volume l q.2 :=
      (hC.mono (Icc_subset_Icc le_rfl (hsnd hq).2)).intervalIntegrable_of_Icc
        (μ := volume) (hsnd hq).1
    exact (intervalIntegral.integral_interval_sub_left hb ha).symm
  have hH : ContinuousOn H T := by
    intro q hq
    have hinv := endpointCompliance_isInvertible (hord q hq).2.1 (hC.mono (hsub q hq))
      (fun t ht p hp ↦ hpos t (hsub q hq ht) p hp)
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun q : ℝ × ℝ ↦ endpointCompliance C q.1 q.2)
      (hinv.contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)).continuousAt (hIntegral q hq)
  have hpositive (q : ℝ × ℝ) (hq : q ∈ T) (v : V) (hv : v ≠ 0) :
      0 < H q v v :=
    endpointCompliance_inverse_pos (hord q hq).2.1 (hC.mono (hsub q hq))
      (fun t ht p hp ↦ hpos t (hsub q hq ht) p hp) hv
  let U := T ×ˢ sphere (0 : V) 1
  let f : (ℝ × ℝ) × V → ℝ := fun q ↦ H q.1 q.2 q.2
  have hU : IsCompact U := hT.prod (isCompact_sphere (0 : V) 1)
  have hf : ContinuousOn f U := by
    have hp : ContinuousOn (fun q : (ℝ × ℝ) × V ↦ H q.1) U :=
      hH.comp continuousOn_fst (fun q hq ↦ hq.1)
    exact (hp.clm_apply continuousOn_snd).clm_apply continuousOn_snd
  obtain ⟨c₀, hc₀, hmin⟩ := hU.exists_forall_le' hf (a := (0 : ℝ)) (by
    intro q hq
    apply hpositive q.1 hq.1 q.2
    intro hzero
    simpa [hzero] using hq.2)
  obtain ⟨M, hmax⟩ := hU.bddAbove_image hf
  refine ⟨hH, c₀, max c₀ M, hc₀, le_max_left _ _, ?_⟩
  intro q hq v
  change c₀ * ‖v‖ ^ 2 ≤ H q v v ∧ H q v v ≤ max c₀ M * ‖v‖ ^ 2
  by_cases hv : v = 0
  · subst v
    simp
  · let w : V := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
    have hmem : (q, w) ∈ U := ⟨hq, by simpa using hw⟩
    have hlo : c₀ ≤ H q w w := hmin (q, w) hmem
    have hhi : H q w w ≤ M := by
      apply hmax
      exact ⟨(q, w), hmem, rfl⟩
    have hvw : ‖v‖ • w = v := by
      change ‖v‖ • (‖v‖⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
    have hscale : H q v v = ‖v‖ ^ 2 * H q w w := by
      calc
        H q v v = H q (‖v‖ • w) (‖v‖ • w) := by rw [hvw]
        _ = ‖v‖ ^ 2 * H q w w := by
          simp only [map_smul, smul_apply, smul_eq_mul]
          ring
    constructor
    · calc
        c₀ * ‖v‖ ^ 2 = ‖v‖ ^ 2 * c₀ := mul_comm _ _
        _ ≤ ‖v‖ ^ 2 * H q w w := mul_le_mul_of_nonneg_left hlo (sq_nonneg _)
        _ = H q v v := hscale.symm
    · calc
        H q v v = ‖v‖ ^ 2 * H q w w := hscale
        _ ≤ ‖v‖ ^ 2 * max c₀ M :=
          mul_le_mul_of_nonneg_left (hhi.trans (le_max_right _ _)) (sq_nonneg _)
        _ = max c₀ M * ‖v‖ ^ 2 := mul_comm _ _

end OTSelector.Geometry

end
end

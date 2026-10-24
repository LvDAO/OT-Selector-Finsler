import OTSelector.Geometry.Finsler.CalibratedDistance.KernelDistanceHessian

/-!
# The original distance jet from local calibration data

The original global distance, its value, first derivative and both Hessian descriptions
are obtained together at the endpoints of a single local calibration curve. Its intrinsic
equation, complete smooth variation family and true minimizing distance branch are derived
internally. The full compliance and restricted length compliance use this same curve.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Actual local affine unit calibration data give the complete original distance jet:
C3 regularity, its length, its momentum gradient, the full energy-compliance Hessian and
the inverse-integral kernel length Hessian. Neither a flow family nor any jet identity
is supplied, and every operator on the right is evaluated along the original curve. -/
theorem endpointDistance_jet_of_local_calibration (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {c : ℝ → M} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hc : ContDiffOn ℝ 2 (extChartAt 𝓘(ℝ, E) old ∘ c) I)
    (hx : ∀ t ∈ I, c t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {a b : ℝ} (hab : a < b) (hseg : Icc a b ⊆ I)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1) {C : ℝ}
    (heq : ∀ y ∈ U, u ((extChartAt 𝓘(ℝ, E) old).symm y) = p y + C)
    (hspace : ∀ t ∈ I, (extChartAt 𝓘(ℝ, E) old ∘ c) t ∈ U)
    (hvelocity : ∀ t ∈ I, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t = v₀) :
    let d : E × E → ℝ := fun q ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal
    let q₀ := ((extChartAt 𝓘(ℝ, E) old ∘ c) a, (extChartAt 𝓘(ℝ, E) old ∘ c) b)
    ContDiffAt ℝ 3 d q₀ ∧ d q₀ = b - a ∧
      fderiv ℝ d q₀ = p.comp (ContinuousLinearMap.snd ℝ E E) -
        p.comp (ContinuousLinearMap.fst ℝ E E) ∧
      (∀ h k : E × E, fderiv ℝ (fderiv ℝ d) q₀ h k =
        (F.chartEndpointCompliance old c a b).inverse (h.2 - h.1) (k.2 - k.1) -
          p (h.2 - h.1) * p (k.2 - k.1) / (b - a)) ∧
      ∀ h k : p.ker × p.ker,
      fderiv ℝ (fderiv ℝ d) q₀
        ((h.1 : E), (h.2 : E)) ((k.1 : E), (k.2 : E)) =
          (F.chartLengthKernelCompliance old p c a b).inverse
            (h.2 - h.1) (k.2 - k.1) := by
  have hcEL := hF.isEulerLagrangeOn_of_affine_calibration_curve old hI hc hx hu
    hU hsub p hp hunit heq hspace hvelocity
  let z₀ := ((extChartAt 𝓘(ℝ, E) old ∘ c) a,
    deriv (extChartAt 𝓘(ℝ, E) old ∘ c) a)
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  obtain ⟨hz, Γ, hEL, hinit, hG, he⟩ := hF.exists_complete_tangentFamily_C2_through_curve
    hcomplete old hI hconn hcEL (hseg ha) (hx a (hseg ha))
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) :
      deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t =
        deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t :=
    ((he.eventuallyEq_of_mem (hI.mem_nhds (hseg ht))).fun_comp
      (extChartAt 𝓘(ℝ, E) old)).deriv_eq
  have hΓx (t : ℝ) (ht : t ∈ Icc a b) :
      Γ z₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source := by
    rw [he (hseg ht)]; exact hx t (hseg ht)
  have hΓspace (t : ℝ) (ht : t ∈ Icc a b) :
      (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t ∈ U := by
    change extChartAt 𝓘(ℝ, E) old (Γ z₀ t) ∈ U
    rw [he (hseg ht)]; exact hspace t (hseg ht)
  have hΓvelocity (t : ℝ) (ht : t ∈ Icc a b) :
      deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t = v₀ :=
    (hderiv t ht).trans (hvelocity t (hseg ht))
  have hcompliance : F.chartEndpointCompliance old (Γ z₀) a b =
      F.chartEndpointCompliance old c a b := by
    apply endpointCompliance_congr_on hab.le
    intro t ht
    dsimp only [chartInverseEnergyHessian]
    rw [hderiv t ht]
    change (verticalEnergyHessian (F.chartEnergy old)
      (extChartAt 𝓘(ℝ, E) old (Γ z₀ t), _)).inverse = _
    rw [he (hseg ht)]
    rfl
  have hq : chartEndpointMap old Γ b z₀ =
      ((extChartAt 𝓘(ℝ, E) old ∘ c) a, (extChartAt 𝓘(ℝ, E) old ∘ c) b) := by
    change (z₀.1, _) = _
    rw [he (hseg hb)]
    rfl
  have hfull := hF.endpointDistance_C3_hessian_of_affine_tube_data hcomplete old
    (z₀ := z₀) hab hEL hinit hG hz hu hΓx hU hsub p hp hunit heq hΓspace hΓvelocity
  dsimp only at hfull ⊢
  rw [hq, hcompliance] at hfull
  refine ⟨hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2, ?_⟩
  exact (hF.endpointDistance_kernelHessian_of_local_calibration hcomplete old hI hconn
    hc hx hab hseg hu hU hsub p hp hunit heq hspace hvelocity).2

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

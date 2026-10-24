import OTSelector.Geometry.FinslerAffineDistanceHessian
import OTSelector.Geometry.Finsler.KernelEndpointCompliance

/-!
# The original endpoint distance and the integrated length Hessian

On a genuine affine unit calibration tube, the actual endpoint distance Hessian on the
calibrated covector kernel is exactly the inverse integral of the inverses of the original
restricted fiber length Hessians. Both the distance and the length Hessians use the same
original Finsler structure and the same intrinsic curve.
-/

open Set Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The actual global distance Hessian on kernel endpoint directions is the inverse
integral of original restricted length-Hessian inverses. All first-variation, Jacobi,
calibration, branch and inverse identifications are derived from the original tube data. -/
theorem endpointDistance_kernelHessian_of_affine_tube_data (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {Γ : (E × E) → ℝ → M} {a b : ℝ} (hab : a < b)
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain old)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hx : ∀ t ∈ Icc a b, Γ z₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1) {C : ℝ}
    (heq : ∀ y ∈ U, u ((extChartAt 𝓘(ℝ, E) old).symm y) = p y + C)
    (hspace : ∀ t ∈ Icc a b, (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t ∈ U)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t = v₀) :
    let d : E × E → ℝ := fun q ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal
    ContDiffAt ℝ 3 d (chartEndpointMap old Γ b z₀) ∧ ∀ h k : p.ker × p.ker,
      fderiv ℝ (fderiv ℝ d) (chartEndpointMap old Γ b z₀)
        ((h.1 : E), (h.2 : E)) ((k.1 : E), (k.2 : E)) =
          (F.chartLengthKernelCompliance old p (Γ z₀) a b).inverse
            (h.2 - h.1) (k.2 - k.1) := by
  have hbound (x : E) (hx : x ∈ U) (v : E) :
      p v ≤ (F.chartLength old (x, v) : ℝ) :=
    hF.chart_covector_le_chartLength old hu hU hsub p heq hx v
  have hmomentum (t : ℝ) (ht : t ∈ Icc a b) :
      (F.chartMomentumFamily old Γ (z₀, t)).2 = p := by
    change fiberLegendre (F.chartEnergy old)
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t) = p
    rw [hvelocity t ht]
    exact (hF.chartEnergy_calibrated_identities old hU hsub p hp hunit hbound
      (hspace t ht)).2.2.1
  have hunit' (t : ℝ) (ht : t ∈ Icc a b) : (F.chartLength old
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t) : ℝ) = 1 := by
    rw [hvelocity t ht]
    exact_mod_cast hunit _ (hspace t ht)
  obtain ⟨hC3, _, _, hH⟩ := hF.endpointDistance_C3_hessian_of_affine_tube_data
    hcomplete old hab hEL hinit hG hz₀ hu hx hU hsub p hp hunit heq hspace hvelocity
  refine ⟨hC3, ?_⟩
  intro h k
  have hh := hH ((h.1 : E), (h.2 : E)) ((k.1 : E), (k.2 : E))
  have hker : p ((h.2 : E) - (h.1 : E)) = 0 := by
    rw [map_sub, show p (h.2 : E) = 0 from h.2.property,
      show p (h.1 : E) = 0 from h.1.property, sub_zero]
  simp only [hker, zero_mul, zero_div, sub_zero] at hh
  exact hh.trans (hF.chartEndpointCompliance_inverse_on_kernel
    (isOpen_chartEnergyDomain old) hEL hG hz₀ old hab hx p v₀
    (by rw [hp]; norm_num) hvelocity hmomentum hunit' (h.2 - h.1) (k.2 - k.1))

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

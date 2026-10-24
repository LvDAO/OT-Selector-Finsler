import OTSelector.Geometry.Finsler.KernelDistanceHessian
import OTSelector.Geometry.FinslerAffineKernelDistanceHessian

/-!
# The original kernel distance Hessian without a supplied geodesic family

Original metric completeness constructs the smooth family from one intrinsic
Euler--Lagrange curve. Initial-value uniqueness identifies its central member with that
curve on its open connected time interval. The actual global endpoint distance therefore
has the inverse-integral length Hessian formula using only the given curve and genuine
local calibration data; a separate flow family or variation is not an input.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}



/-- For a single intrinsic curve in an actual affine calibration tube, the true global
endpoint distance is C3 and its kernel Hessian is the inverse integral of the original
restricted length-Hessian inverses. The complete smooth family is constructed internally. -/
theorem endpointDistance_kernelHessian_of_calibrated_curve (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {c : ℝ → M} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hc : F.IsEulerLagrangeOn c I) {a b : ℝ} (hab : a < b) (hseg : Icc a b ⊆ I)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hx : ∀ t ∈ Icc a b, c t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1) {C : ℝ}
    (heq : ∀ y ∈ U, u ((extChartAt 𝓘(ℝ, E) old).symm y) = p y + C)
    (hspace : ∀ t ∈ Icc a b, (extChartAt 𝓘(ℝ, E) old ∘ c) t ∈ U)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t = v₀) :
    let d : E × E → ℝ := fun q ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal
    let q₀ := ((extChartAt 𝓘(ℝ, E) old ∘ c) a, (extChartAt 𝓘(ℝ, E) old ∘ c) b)
    ContDiffAt ℝ 3 d q₀ ∧ ∀ h k : p.ker × p.ker,
      fderiv ℝ (fderiv ℝ d) q₀
        ((h.1 : E), (h.2 : E)) ((k.1 : E), (k.2 : E)) =
          (F.chartLengthKernelCompliance old p c a b).inverse
            (h.2 - h.1) (k.2 - k.1) := by
  let z₀ := ((extChartAt 𝓘(ℝ, E) old ∘ c) a,
    deriv (extChartAt 𝓘(ℝ, E) old ∘ c) a)
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  obtain ⟨hz, Γ, hEL, hinit, hG, he⟩ := hF.exists_complete_tangentFamily_C2_through_curve
    hcomplete old hI hconn hc (hseg ha) (hx a ha)
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) :
      deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t =
        deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t :=
    ((he.eventuallyEq_of_mem (hI.mem_nhds (hseg ht))).fun_comp
      (extChartAt 𝓘(ℝ, E) old)).deriv_eq
  have hΓx (t : ℝ) (ht : t ∈ Icc a b) :
      Γ z₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source := by
    rw [he (hseg ht)]; exact hx t ht
  have hΓspace (t : ℝ) (ht : t ∈ Icc a b) :
      (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t ∈ U := by
    change extChartAt 𝓘(ℝ, E) old (Γ z₀ t) ∈ U
    rw [he (hseg ht)]; exact hspace t ht
  have hΓvelocity (t : ℝ) (ht : t ∈ Icc a b) :
      deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t = v₀ :=
    (hderiv t ht).trans (hvelocity t ht)
  have hcompliance : F.chartLengthKernelCompliance old p (Γ z₀) a b =
      F.chartLengthKernelCompliance old p c a b := by
    apply endpointCompliance_congr_on hab.le
    intro t ht
    dsimp only
    rw [hderiv t ht]
    change (F.chartLengthKernelHessian old p
      (extChartAt 𝓘(ℝ, E) old (Γ z₀ t), _)).inverse = _
    rw [he (hseg ht)]
    rfl
  have hq : chartEndpointMap old Γ b z₀ =
      ((extChartAt 𝓘(ℝ, E) old ∘ c) a, (extChartAt 𝓘(ℝ, E) old ∘ c) b) := by
    change (z₀.1, _) = _
    rw [he (hseg hb)]
    rfl
  have h := hF.endpointDistance_kernelHessian_of_affine_tube_data hcomplete old (z₀ := z₀) hab
    hEL hinit hG hz hu hΓx hU hsub p hp hunit heq hΓspace hΓvelocity
  simpa only [hq, hcompliance] using h



/-- Pure local affine calibration data give the original global kernel distance Hessian.
Both the intrinsic equation and the complete smooth variation family are consequences
of these data and original metric completeness, not supplied assumptions. -/
theorem endpointDistance_kernelHessian_of_local_calibration (hF : F.IsSmoothStronglyConvex)
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
    ContDiffAt ℝ 3 d q₀ ∧ ∀ h k : p.ker × p.ker,
      fderiv ℝ (fderiv ℝ d) q₀
        ((h.1 : E), (h.2 : E)) ((k.1 : E), (k.2 : E)) =
          (F.chartLengthKernelCompliance old p c a b).inverse
            (h.2 - h.1) (k.2 - k.1) := by
  have hEL := hF.isEulerLagrangeOn_of_affine_calibration_curve old hI hc hx hu
    hU hsub p hp hunit heq hspace hvelocity
  exact hF.endpointDistance_kernelHessian_of_calibrated_curve hcomplete old hI hconn
    hEL hab hseg hu (fun t ht ↦ hx t (hseg ht)) hU hsub p hp hunit heq
    (fun t ht ↦ hspace t (hseg ht)) (fun t ht ↦ hvelocity t (hseg ht))

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

import OTSelector.Geometry.FinslerEndpointDistanceHessian

/-!
# Original distance Hessian from an affine calibration tube

The original global Lipschitz potential supplies the entire covector bound. Its genuine
unit-velocity tube constructs minimality, endpoint nonconjugacy, the same endpoint inverse,
and the original minimizing distance branch. The resulting distance is C3 and has the
proved compliance Hessian, with no branch, gradient, or Hessian identity assumed.
-/

open Set Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- A genuine affine calibration tube gives the original endpoint distance C3
regularity and its explicit full Hessian. Original global Lipschitz calibration derives
all comparison bounds, minimality, endpoint invertibility and branch identification. -/
theorem endpointDistance_C3_hessian_of_affine_tube_data (hF : F.IsSmoothStronglyConvex)
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
    ContDiffAt ℝ 3 d (chartEndpointMap old Γ b z₀) ∧
      d (chartEndpointMap old Γ b z₀) = b - a ∧
      fderiv ℝ d (chartEndpointMap old Γ b z₀) =
        p.comp (ContinuousLinearMap.snd ℝ E E) -
          p.comp (ContinuousLinearMap.fst ℝ E E) ∧ ∀ h k : E × E,
      fderiv ℝ (fderiv ℝ d) (chartEndpointMap old Γ b z₀) h k =
        (F.chartEndpointCompliance old (Γ z₀) a b).inverse
          (h.2 - h.1) (k.2 - k.1) - p (h.2 - h.1) * p (k.2 - k.1) / (b - a) := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  have hbound (x : E) (hx : x ∈ U) (v : E) :
      p v ≤ (F.chartLength old (x, v) : ℝ) :=
    hF.chart_covector_le_chartLength old hu hU hsub p heq hx v
  obtain ⟨hdu, hmin, hsat, _, _, hlength, _⟩ := hF.affine_calibration_tube_data old hab
    (hEL z₀ hz₀) hu hx hU p hp hunit heq hspace hvelocity
  have hinv := hF.isInvertible_chartEndpointMap_of_calibrated_tube old hab hEL hinit hG
    hz₀ hx hU hsub p hp hunit hbound hspace hvelocity
  obtain ⟨e, W, I, he, hze, hzW, hsube, _, hi, hW, hWe, hWB, hI, hconn, hseg,
    hmap, hbranch, _, hgrad, _, _, hC3⟩ :=
    hF.exists_calibrated_endpointDistanceC3 hcomplete old hab hEL hinit hG hz₀ hmin
      hu hsat hdu hx hinv
  have hq₀ : e.symm (chartEndpointMap old Γ b z₀) = z₀ := by
    rw [← he]
    exact e.left_inv hze
  have hd₀ := congrArg ENNReal.toReal (hbranch _ hzW).2.2.1
  rw [hq₀, hlength, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)] at hd₀
  have hm (t : ℝ) (ht : t ∈ Icc a b) :
      F.endpointLengthMomentum old Γ e t (chartEndpointMap old Γ b z₀) = p := by
    dsimp only [endpointLengthMomentum, endpointChartPhase]
    rw [hq₀, hvelocity t ht]
    exact (hF.chartEnergy_calibrated_identities old hU hsub p hp hunit hbound
      (hspace t ht)).1
  have hd₁ := (hgrad _ hzW).fderiv
  change _ = (F.endpointLengthMomentum old Γ e b _).comp _ -
    (F.endpointLengthMomentum old Γ e a _).comp _ at hd₁
  rw [hm b (right_mem_Icc.mpr hab.le), hm a (left_mem_Icc.mpr hab.le)] at hd₁
  refine ⟨hC3.contDiffAt (hW.mem_nhds hzW), hd₀, hd₁, ?_⟩
  intro h k
  have hend (q : E × E) (hq : q ∈ W) :
      extChartAt 𝓘(ℝ, E) old (Γ (e.symm q) a) = q.1 ∧
      extChartAt 𝓘(ℝ, E) old (Γ (e.symm q) b) = q.2 := by
    constructor
    · rw [(hbranch q hq).1]
      exact (extChartAt 𝓘(ℝ, E) old).right_inv (hWB hq).1
    · rw [(hbranch q hq).2.1]
      exact (extChartAt 𝓘(ℝ, E) old).right_inv (hWB hq).2
  have hh := hF.endpointDistance_hessian_of_calibrated_branch old hEL hG hsube hi hW
    hWe hzW hI hconn hab hseg hmap hend
    (fun q hq ↦ congrArg ENNReal.toReal (hbranch q hq).2.2.1) hU hsub p hp
    (fun x hx ↦ by exact_mod_cast hunit x hx) hbound
    (by simpa only [hq₀, Function.comp_def] using hspace) (by simpa only [hq₀] using hvelocity) h k
  simpa only [hq₀] using hh

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

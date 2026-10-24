import OTSelector.Analysis.CubicTaylor
import OTSelector.Geometry.FinslerAffineDistanceHessian
import OTSelector.Geometry.FinslerLocalDistanceJet

/-!
# Cubic error for the actual Finsler distance expansion

The affine calibration tube determines the value, first derivative and full Hessian
of the original distance. Its genuine C3 regularity supplies one cubic error constant
for all sufficiently small endpoint displacements. On the fixed momentum kernel the
quadratic coefficient is the inverse integral of actual restricted length-Hessian inverses.
-/

open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

private theorem affine_tube_kernel_coefficient (hF : F.IsSmoothStronglyConvex)
    (old : M) {Γ : (E × E) → ℝ → M} {a b : ℝ} (hab : a < b)
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ)
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
    ∀ α β : p.ker,
      (F.chartEndpointCompliance old (Γ z₀) a b).inverse (β - α : p.ker) (β - α : p.ker) =
        (F.chartLengthKernelCompliance old p (Γ z₀) a b).inverse (β - α) (β - α) := by
  have hbound (x : E) (hx : x ∈ U) (v : E) :
      p v ≤ (F.chartLength old (x, v) : ℝ) :=
    hF.chart_covector_le_chartLength old hu hU hsub p heq hx v
  have hm (t : ℝ) (ht : t ∈ Icc a b) : (F.chartMomentumFamily old Γ (z₀, t)).2 = p := by
    change fiberLegendre (F.chartEnergy old)
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t) = p
    rw [hvelocity t ht]
    exact (hF.chartEnergy_calibrated_identities old hU hsub p hp hunit hbound
      (hspace t ht)).2.2.1
  have hn (t : ℝ) (ht : t ∈ Icc a b) :
      (F.chartLength old ((extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t) : ℝ) = 1 := by
    rw [hvelocity t ht, hunit _ (hspace t ht)]
    rfl
  intro α β
  exact hF.chartEndpointCompliance_inverse_on_kernel (isOpen_chartEnergyDomain old)
    hEL hG hz₀ old hab hx p v₀ (by rw [hp]; exact one_ne_zero) hvelocity hm hn
    (β - α) (β - α)

/-- The original distance has its calibrated quadratic expansion with a single cubic
error constant for all sufficiently small displacements of both actual endpoints. -/
theorem endpointDistance_taylor_of_affine_tube_data (hF : F.IsSmoothStronglyConvex)
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
    ∃ r > 0, ∃ K ≥ 0, ∀ α β : E, ‖(α, β)‖ ≤ r →
      |d (chartEndpointMap old Γ b z₀ + (α, β)) - (b - a) - p (β - α) -
        (1 / 2 : ℝ) * ((F.chartEndpointCompliance old (Γ z₀) a b).inverse
          (β - α) (β - α) - (p (β - α)) ^ 2 / (b - a))| ≤ K * ‖(α, β)‖ ^ 3 := by
  obtain ⟨hC3, hzero, hfirst, hsecond⟩ :=
    hF.endpointDistance_C3_hessian_of_affine_tube_data hcomplete old hab hEL hinit hG
      hz₀ hu hx hU hsub p hp hunit heq hspace hvelocity
  obtain ⟨r, hr, K, hK, hrem⟩ := exists_quadratic_taylor_remainder_bound_of_contDiffAt hC3
  refine ⟨r, hr, K, hK, ?_⟩
  intro α β hsmall
  have h := hrem (α, β) hsmall
  dsimp only at hzero
  rw [hzero, hfirst, hsecond] at h
  simpa only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst, Prod.snd, _root_.map_sub,
    pow_two, Real.norm_eq_abs] using h

/-- On the actual calibrated momentum kernel, the distance expansion has zero linear
term and the inverse integrated original length Hessian as its quadratic coefficient. -/
theorem endpointDistance_taylor_on_kernel_of_affine_tube_data
    (hF : F.IsSmoothStronglyConvex)
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
    ∃ r > 0, ∃ K ≥ 0, ∀ α β : p.ker, ‖((α : E), (β : E))‖ ≤ r →
      |d (chartEndpointMap old Γ b z₀ + ((α : E), (β : E))) - (b - a) -
        (1 / 2 : ℝ) * (F.chartLengthKernelCompliance old p (Γ z₀) a b).inverse
          (β - α) (β - α)| ≤ K * ‖((α : E), (β : E))‖ ^ 3 := by
  obtain ⟨r, hr, K, hK, hrem⟩ :=
    hF.endpointDistance_taylor_of_affine_tube_data hcomplete old hab hEL hinit hG
      hz₀ hu hx hU hsub p hp hunit heq hspace hvelocity
  refine ⟨r, hr, K, hK, ?_⟩
  intro α β hsmall
  have h := hrem α β hsmall
  have hcoeff := affine_tube_kernel_coefficient hF old hab hEL hG hz₀ hu hx hU hsub
    p hp hunit heq hspace hvelocity α β
  have hker : p ((β : E) - (α : E)) = 0 := by
    exact (β - α).property
  have hcoeff' : (F.chartEndpointCompliance old (Γ z₀) a b).inverse
      ((β : E) - (α : E)) ((β : E) - (α : E)) =
      (F.chartLengthKernelCompliance old p (Γ z₀) a b).inverse (β - α) (β - α) := by
    simpa only [Submodule.coe_sub] using hcoeff
  rw [hker, hcoeff'] at h
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, sub_zero] using h

/-- On a compact set of actual calibrated endpoint pairs, one radius and one cubic
constant work simultaneously. The genuine family and its two times may vary with the
center; all value, gradient and Hessian identities follow from its actual tube data. -/
theorem endpointDistance_taylor_uniform_on_compact_of_affine_tube_data
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {K : Set (E × E)} (hK : IsCompact K)
    (Γ : (E × E) → (E × E) → ℝ → M) (a b : E × E → ℝ)
    (hab : ∀ q ∈ K, a q < b q)
    (hEL : ∀ q ∈ K, ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ q z) univ)
    (hinit : ∀ q ∈ K, ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q z) ⟨a q, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ∀ q ∈ K,
      ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun r ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q r.1) ⟨r.2, (1 : ℝ)⟩)
        (chartEnergyDomain old ×ˢ univ))
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1) {C : ℝ}
    (heq : ∀ y ∈ U, u ((extChartAt 𝓘(ℝ, E) old).symm y) = p y + C)
    (ζ : E × E → E × E) (hz : ∀ q ∈ K, ζ q ∈ chartEnergyDomain old)
    (hend : ∀ q ∈ K, chartEndpointMap old (Γ q) (b q) (ζ q) = q)
    (hx : ∀ q ∈ K, ∀ t ∈ Icc (a q) (b q),
      Γ q (ζ q) t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hspace : ∀ q ∈ K, ∀ t ∈ Icc (a q) (b q),
      (extChartAt 𝓘(ℝ, E) old ∘ Γ q (ζ q)) t ∈ U)
    (hvelocity : ∀ q ∈ K, ∀ t ∈ Icc (a q) (b q),
      deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ q (ζ q)) t = v₀) :
    let d : E × E → ℝ := fun q ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal
    ∃ r > 0, ∃ A ≥ 0, ∀ q ∈ K, ∀ α β : E, ‖(α, β)‖ ≤ r →
      |d (q + (α, β)) - (b q - a q) - p (β - α) -
        (1 / 2 : ℝ) * ((F.chartEndpointCompliance old (Γ q (ζ q)) (a q) (b q)).inverse
          (β - α) (β - α) - (p (β - α)) ^ 2 / (b q - a q))| ≤ A * ‖(α, β)‖ ^ 3 := by
  let d : E × E → ℝ := fun q ↦
    (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
      ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal
  have hjets (q : E × E) (hq : q ∈ K) :
      ContDiffAt ℝ 3 d q ∧ d q = b q - a q ∧
        fderiv ℝ d q = p.comp (ContinuousLinearMap.snd ℝ E E) -
          p.comp (ContinuousLinearMap.fst ℝ E E) ∧ ∀ h k : E × E,
        fderiv ℝ (fderiv ℝ d) q h k =
          (F.chartEndpointCompliance old (Γ q (ζ q)) (a q) (b q)).inverse
            (h.2 - h.1) (k.2 - k.1) -
              p (h.2 - h.1) * p (k.2 - k.1) / (b q - a q) := by
    have h := hF.endpointDistance_C3_hessian_of_affine_tube_data hcomplete old (hab q hq)
      (hEL q hq) (hinit q hq) (hG q hq) (hz q hq) hu (hx q hq) hU hsub p hp hunit heq
      (hspace q hq) (hvelocity q hq)
    rwa [hend q hq] at h
  let O : Set (E × E) := {q | ContDiffAt ℝ 3 d q}
  have hO : IsOpen O := isOpen_iff_mem_nhds.mpr fun q hq ↦
    (show ContDiffAt ℝ 3 d q from hq).eventually (by norm_num)
  have hdiff : ContDiffOn ℝ 3 d O := fun q hq ↦ (show ContDiffAt ℝ 3 d q from hq).contDiffWithinAt
  have hKO : K ⊆ O := fun q hq ↦ (hjets q hq).1
  obtain ⟨r, hr, A, hA, hrem⟩ :=
    exists_uniform_quadratic_taylor_remainder_bound hO hdiff hK hKO
  refine ⟨r, hr, A, hA, ?_⟩
  intro q hq α β hsmall
  have h := hrem q hq (α, β) hsmall
  obtain ⟨_, hzero, hfirst, hsecond⟩ := hjets q hq
  rw [hzero, hfirst, hsecond] at h
  simpa only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst, Prod.snd, _root_.map_sub,
    pow_two, Real.norm_eq_abs] using h

/-- Local affine calibration alone gives the actual original-distance expansion, both
in full endpoint coordinates and on its momentum kernel, with the same cubic constant.
The intrinsic equation and complete variation family are constructed by the jet theorem. -/
theorem endpointDistance_taylor_of_local_calibration (hF : F.IsSmoothStronglyConvex)
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
    ∃ r > 0, ∃ K ≥ 0,
      (∀ α β : E, ‖(α, β)‖ ≤ r →
        |d (q₀ + (α, β)) - (b - a) - p (β - α) -
          (1 / 2 : ℝ) * ((F.chartEndpointCompliance old c a b).inverse
            (β - α) (β - α) - (p (β - α)) ^ 2 / (b - a))| ≤ K * ‖(α, β)‖ ^ 3) ∧
      ∀ α β : p.ker, ‖((α : E), (β : E))‖ ≤ r →
        |d (q₀ + ((α : E), (β : E))) - (b - a) -
          (1 / 2 : ℝ) * (F.chartLengthKernelCompliance old p c a b).inverse
            (β - α) (β - α)| ≤ K * ‖((α : E), (β : E))‖ ^ 3 := by
  obtain ⟨hC3, hzero, hfirst, hsecond, hkernel⟩ :=
    hF.endpointDistance_jet_of_local_calibration hcomplete old hI hconn hc hx hab hseg
      hu hU hsub p hp hunit heq hspace hvelocity
  obtain ⟨r, hr, K, hK, hrem⟩ := exists_quadratic_taylor_remainder_bound_of_contDiffAt hC3
  refine ⟨r, hr, K, hK, ?_, ?_⟩
  · intro α β hsmall
    have h := hrem (α, β) hsmall
    dsimp only at hzero
    rw [hzero, hfirst, hsecond] at h
    simpa only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst, Prod.snd,
      _root_.map_sub,
      pow_two, Real.norm_eq_abs] using h
  · intro α β hsmall
    have h := hrem ((α : E), (β : E)) hsmall
    dsimp only at hzero
    rw [hzero, hfirst, hkernel (α, β) (α, β)] at h
    simpa only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst, Prod.snd,
      show p (α : E) = 0 from α.property, show p (β : E) = 0 from β.property,
      sub_self, sub_zero, Real.norm_eq_abs] using h

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

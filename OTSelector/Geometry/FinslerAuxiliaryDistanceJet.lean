import OTSelector.Geometry.Finsler.CalibratedDistance.KernelDistanceHessian

/-!
# Separate global calibration and the local auxiliary distance jet

The original rough potential is used only to select the unique globally minimizing
central segment. An independent local auxiliary calibration supplies the actual Finsler
unit velocity and covector bound used for nonconjugacy and the Hessian computation.
No globally Lipschitz extension of the auxiliary potential, or neighborhood agreement
with the original potential, is required. The true global distance branch is constructed.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The actual original distance jet from separate central global calibration and local
auxiliary unit-calibration data. The original globally Lipschitz potential is required
only at the central segment and its initial differential; it need not equal an affine
function on the auxiliary tube. All endpoint inverses and distance identities are derived. -/
theorem endpointDistance_jet_of_auxiliary_tube (hF : F.IsSmoothStronglyConvex)
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
    (hmin₀ : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Γ z₀ a) (Γ z₀ b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z₀) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Γ z₀ b) - u (Γ z₀ a) = dist (Γ z₀ a) (Γ z₀ b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Γ z₀ a))
    (hx : ∀ t ∈ Icc a b, Γ z₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1)
    (hbound : ∀ x ∈ U, ∀ v : E, p v ≤ (F.chartLength old (x, v) : ℝ))
    (hspace : ∀ t ∈ Icc a b, (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t ∈ U)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t = v₀) :
    let d : E × E → ℝ := fun q ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal
    ContDiffAt ℝ 3 d (chartEndpointMap old Γ b z₀) ∧
      d (chartEndpointMap old Γ b z₀) = b - a ∧
      fderiv ℝ d (chartEndpointMap old Γ b z₀) =
        p.comp (ContinuousLinearMap.snd ℝ E E) -
          p.comp (ContinuousLinearMap.fst ℝ E E) ∧ (∀ h k : E × E,
      fderiv ℝ (fderiv ℝ d) (chartEndpointMap old Γ b z₀) h k =
        (F.chartEndpointCompliance old (Γ z₀) a b).inverse
          (h.2 - h.1) (k.2 - k.1) - p (h.2 - h.1) * p (k.2 - k.1) / (b - a)) ∧
      ∀ h k : p.ker × p.ker,
        fderiv ℝ (fderiv ℝ d) (chartEndpointMap old Γ b z₀)
          ((h.1 : E), (h.2 : E)) ((k.1 : E), (k.2 : E)) =
            (F.chartLengthKernelCompliance old p (Γ z₀) a b).inverse
              (h.2 - h.1) (k.2 - k.1) := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hphase₀ := hF.chartPhase_of_tangent_eq (hEL z₀ hz₀ a (mem_univ _)) old hz₀
    (hinit z₀ hz₀)
  have hunit₀ : F.chartLength old z₀ = 1 := by
    rw [← hphase₀, hvelocity a ha]
    exact hunit _ (hspace a ha)
  have hspeed (t : ℝ) : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z₀)
      ⟨t, (1 : ℝ)⟩) = F.chartLength old z₀ := by
    rw [hF.speed_eq_of_isEulerLagrangeOn (hEL z₀ hz₀) isPreconnected_univ
      (mem_univ t) (mem_univ a), hinit z₀ hz₀]
    rfl
  have hlength : pathELength 𝓘(ℝ, E) (Γ z₀) a b = ENNReal.ofReal (b - a) := by
    have hh := F.pathELength_eq_of_constant_speed (a := a) (b := b) (fun t _ ↦
      hspeed t)
    simpa only [hunit₀, ENNReal.coe_one, one_mul] using hh
  have hinv := hF.isInvertible_chartEndpointMap_of_calibrated_tube old hab hEL hinit hG
    hz₀ hx hU hsub p hp hunit hbound hspace hvelocity
  obtain ⟨e, W, I, he, hze, hzW, hsube, _, hi, hW, hWe, hWB, hI, hconn, hseg,
    hmap, hbranch, _, hgrad, _, _, hC3⟩ :=
    hF.exists_calibrated_endpointDistanceC3 hcomplete old hab hEL hinit hG hz₀ hmin₀
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
  rw [hm b hb, hm a ha] at hd₁
  have hH (h k : E × E) :
      fderiv ℝ (fderiv ℝ (fun q : E × E ↦
        (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
          ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal))
          (chartEndpointMap old Γ b z₀) h k =
        (F.chartEndpointCompliance old (Γ z₀) a b).inverse
          (h.2 - h.1) (k.2 - k.1) - p (h.2 - h.1) * p (k.2 - k.1) / (b - a) := by
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
      (by simpa only [hq₀, Function.comp_def] using hspace)
      (by simpa only [hq₀] using hvelocity) h k
    simpa only [hq₀] using hh
  refine ⟨hC3.contDiffAt (hW.mem_nhds hzW), hd₀, hd₁, hH, ?_⟩
  intro h k
  have hh := hH ((h.1 : E), (h.2 : E)) ((k.1 : E), (k.2 : E))
  have hker : p ((h.2 : E) - (h.1 : E)) = 0 := by
    rw [map_sub, show p (h.2 : E) = 0 from h.2.property,
      show p (h.1 : E) = 0 from h.1.property, sub_zero]
  simp only [hker, zero_mul, zero_div, sub_zero] at hh
  apply hh.trans
  refine hF.chartEndpointCompliance_inverse_on_kernel
    (isOpen_chartEnergyDomain old) hEL hG hz₀ old hab hx p v₀
    (by rw [hp]; norm_num) hvelocity ?_ ?_ (h.2 - h.1) (k.2 - k.1)
  · intro t ht
    change fiberLegendre (F.chartEnergy old)
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t) = p
    rw [hvelocity t ht]
    exact (hF.chartEnergy_calibrated_identities old hU hsub p hp hunit hbound
      (hspace t ht)).2.2.1
  · intro t ht
    rw [hvelocity t ht]
    exact_mod_cast hunit _ (hspace t ht)

/-- A single local intrinsic central curve suffices for the auxiliary jet theorem.
Completeness constructs the actual smooth family internally, while global calibration
of the original rough potential and the independent local covector bound remain separate. -/
theorem endpointDistance_jet_of_auxiliary_curve (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {c : ℝ → M} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hc : F.IsEulerLagrangeOn c I) {a b : ℝ} (hab : a < b) (hseg : Icc a b ⊆ I)
    (hmin₀ : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (c a) (c b) = Manifold.pathELength 𝓘(ℝ, E) c a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (c b) - u (c a) = dist (c a) (c b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a))
    (hx : ∀ t ∈ Icc a b, c t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1)
    (hbound : ∀ x ∈ U, ∀ v : E, p v ≤ (F.chartLength old (x, v) : ℝ))
    (hspace : ∀ t ∈ Icc a b, (extChartAt 𝓘(ℝ, E) old ∘ c) t ∈ U)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t = v₀) :
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
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
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
  have hminΓ : F.lengthEDist (Γ z₀ a) (Γ z₀ b) =
      pathELength 𝓘(ℝ, E) (Γ z₀) a b := by
    rw [pathELength_congr (I := 𝓘(ℝ, E)) (he.mono hseg), he (hseg ha), he (hseg hb)]
    exact hmin₀
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
  have hkernel : F.chartLengthKernelCompliance old p (Γ z₀) a b =
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
  have hjet := hF.endpointDistance_jet_of_auxiliary_tube hcomplete old (z₀ := z₀)
    hab hEL hinit hG hz hminΓ hu
    (by rw [he (hseg ha), he (hseg hb)]; exact hsat)
    (by rw [he (hseg ha)]; exact hdu)
    hΓx hU hsub p hp hunit hbound hΓspace hΓvelocity
  dsimp only at hjet ⊢
  simpa only [hq, hcompliance, hkernel] using hjet

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

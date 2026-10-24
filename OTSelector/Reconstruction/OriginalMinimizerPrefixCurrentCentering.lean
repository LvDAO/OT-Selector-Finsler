import OTSelector.Reconstruction.FinslerOriginalInvariantPathCurrentCentering
import OTSelector.Reconstruction.FinslerOriginalWeightedStationaryMinimizer
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic
import OTSelector.Reconstruction.OriginalCompletePathSlabDivergence

/-! Deterministic clock prefixes and slabs of the actual original minimizing
current have zero invariant conditional mean. Original complete-path first
moments supply joint clock/scene integrability, including focal endpoints. -/
open Set Function Filter MeasureTheory Matrix Module Manifold ProbabilityTheory
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator BigOperators ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

private theorem integral_physicalPairKernel_eq_finite_sum
    {q : ℕ} {I Y : Type*} [Fintype I]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (scene : LegalMarkedOptimalInputScene q) (edges : I → LegalMarkedPhysicalEdge q)
    (hplan : (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)) = ∑ i, Measure.dirac (edges i))
    (value : ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) → Y) :
    (∫ p, value p ∂physicalScenePairKernel scene.1) =
      ∑ i, value (physicalPairAnchor (edges i)) := by
  classical
  rw [physicalScenePairKernel_apply,hplan,
    Measure.map_finset_sum' measurable_physicalPairAnchor.aemeasurable]
  simp_rw [Measure.map_dirac' measurable_physicalPairAnchor]
  rw [integral_finsetSum_measure (fun i _ ↦ integrable_dirac (by simp))]
  simp only [integral_dirac]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

private theorem stronglyMeasurable_marked_pathClockWindowReadout_joint
    (q : ℕ) (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (f : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (hd : Measurable d) (hf : Measurable f)
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η) :
    StronglyMeasurable (fun z : LegalMarkedOptimalInputScene q × ℝ ↦
      legalMarkedPathWindowReadout q (fun m ↦ d (m,z.2)) η (fun m ↦ f (m,z.2)) z.1) := by
  let κ : Kernel (LegalMarkedOptimalInputScene q × ℝ)
      ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) :=
    (physicalScenePairKernel (ι := Fin q)).comap
      (fun z : LegalMarkedOptimalInputScene q × ℝ ↦ z.1.1) measurable_fst.fst
  have hmc : Measurable (fun z : (LegalMarkedOptimalInputScene q × ℝ) ×
      ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) ↦ (z.2.2,z.1.2)) :=
    measurable_snd.snd.prodMk measurable_fst.snd
  have hpos : Measurable (fun z : (LegalMarkedOptimalInputScene q × ℝ) ×
      ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) ↦ z.2.1+d (z.2.2,z.1.2)) :=
    measurable_snd.fst.add (hd.comp hmc)
  have hG : Measurable (fun z : (LegalMarkedOptimalInputScene q × ℝ) ×
      ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) ↦
      η (z.2.1+d (z.2.2,z.1.2)) • f (z.2.2,z.1.2)) :=
    (hη.comp hpos).smul (hf.comp hmc)
  have hread : StronglyMeasurable (fun z : LegalMarkedOptimalInputScene q × ℝ ↦
      ∫ p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q),
        η (p.1+d (p.2,z.2)) • f (p.2,z.2) ∂κ z) :=
    hG.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
  simpa only [κ,Kernel.comap_apply,legalMarkedPathWindowReadout] using hread

/-- The actual original path-window current is jointly measurable in scene
and physical clock, with no integrability or centering assumption. -/
theorem stronglyMeasurable_original_pathClockWindowReadout_joint
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η) :
    StronglyMeasurable (fun z : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × ℝ ↦
      legalMarkedPathWindowReadout (finrank ℝ S.covector.ker)
        (originalSeedPathOffset S w z.2) η (originalSeedClockOccupation S w z.2) z.1) := by
  exact stronglyMeasurable_marked_pathClockWindowReadout_joint _
    (fun z ↦ originalSeedPathOffset S w z.2 z.1)
    (fun z ↦ originalSeedClockOccupation S w z.2 z.1)
    (measurable_originalSeedPathOffset_joint S hF hw)
    (measurable_originalSeedClockOccupation S hF hw) hη

/-- Total clock norm of the same current is bounded by its literal absolute
complete-path traffic. No source or target is selected by a spatial cube. -/
theorem lintegral_original_pathClockWindowReadout_norm_le_traffic
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (∫⁻ c : ℝ, ENNReal.ofReal ‖legalMarkedPathWindowReadout (finrank ℝ S.covector.ker)
      (originalSeedPathOffset S w c) η (originalSeedClockOccupation S w c) scene‖) ≤
      originalSeedCompletePathAbsoluteTraffic S w (fun x ↦ |η x|) scene := by
  let q := finrank ℝ S.covector.ker
  let H := fun z : ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) × ℝ ↦
    ENNReal.ofReal |η (z.1.1+originalSeedPathOffset S w z.2 z.1.2)| *
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1.2‖
  have hmc : Measurable (fun z : ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) × ℝ ↦
      (z.1.2,z.2)) := measurable_fst.snd.prodMk measurable_snd
  have hH : Measurable H :=
    ((hη.comp (measurable_fst.fst.add
      ((measurable_originalSeedPathOffset_joint S hF hw).comp hmc))).abs.ennreal_ofReal).mul
        (((measurable_originalSeedClockOccupation S hF hw).comp hmc).norm.ennreal_ofReal)
  calc
    _ ≤ ∫⁻ c : ℝ, ∫⁻ p, H (p,c) ∂physicalScenePairKernel scene.1 := by
      apply lintegral_mono
      intro c
      change ENNReal.ofReal ‖∫ p, η (p.1+originalSeedPathOffset S w c p.2) •
        originalSeedClockOccupation S w c p.2 ∂physicalScenePairKernel scene.1‖ ≤ _
      have hnorm := enorm_integral_le_lintegral_enorm
        (μ := physicalScenePairKernel scene.1)
        (fun p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
          η (p.1+originalSeedPathOffset S w c p.2) • originalSeedClockOccupation S w c p.2)
      simpa only [H,enorm_smul,Real.enorm_eq_ofReal_abs,ofReal_norm] using hnorm
    _ = _ := by
      change (∫⁻ c : ℝ, ∫⁻ p, H (p,c) ∂physicalScenePairKernel scene.1) =
        ∫⁻ p, ∫⁻ c : ℝ, H (p,c) ∂volume ∂physicalScenePairKernel scene.1
      exact (lintegral_lintegral_swap hH.aemeasurable).symm

/-- Clock restriction of the actual original path-window current. Its spatial
window is evaluated along the complete path, without filtering physical endpoints. -/
def originalSeedPathClockSetCurrent (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  ∫ c in A, legalMarkedPathWindowReadout (finrank ℝ S.covector.ker)
    (originalSeedPathOffset S w c) η (originalSeedClockOccupation S w c) scene

/-- The same original unit-window current integrated through a deterministic prefix. -/
def originalSeedPathPrefixCurrent (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (t : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  originalSeedPathClockSetCurrent S w (legalMarkedUnitWindowWeight (finrank ℝ S.covector.ker))
    (Iic t) scene

/-- The same original unit-window current integrated on its deterministic clock slab. -/
def originalSeedPathSlabCurrent (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (s t : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  originalSeedPathClockSetCurrent S w (legalMarkedUnitWindowWeight (finrank ℝ S.covector.ker))
    (Ioc s t) scene

/-- On a genuine finite first plan, the SAME actual current is the sum of
its original full-path edge occupations, including edges with endpoints
outside the spatial observation window. -/
theorem original_pathClockWindowReadout_eq_finite_sum
    {I : Type*} [Fintype I] (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (edges : I → LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (hplan : (scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) =
      ∑ i, Measure.dirac (edges i))
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (c : ℝ) :
    legalMarkedPathWindowReadout (finrank ℝ S.covector.ker)
      (originalSeedPathOffset S w c) η (originalSeedClockOccupation S w c) scene =
    ∑ i, η (originalSeedCompletePath S w (edges i).1.1 (physicalPairAnchor (edges i)).2 c) •
      originalSeedClockOccupation S w c (physicalPairAnchor (edges i)).2 := by
  unfold legalMarkedPathWindowReadout
  rw [integral_physicalPairKernel_eq_finite_sum scene edges hplan]
  apply Finset.sum_congr rfl
  intro i _
  rw [originalSeedCompletePath_eq_anchor_add_offset]
  rfl

/-- Weak slab readout of the actual first scene plan on its original complete
paths. The original momentum is fixed before either clock cut is made. -/
def originalSeedPathWeakSlabReadout (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (s t : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  ∫ p, (∫ r in max p.2.1.1 (min s p.2.1.2)..max p.2.1.1 (min t p.2.1.2),
    fderiv ℝ φ (originalSeedCompletePath S w p.1 p.2 r)
      (originalSeedKernel S w (r - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w p.2)
    ∂volume) ∂physicalScenePairKernel scene.1

/-- The actual scene weak readout is exactly the earlier finite slab flux
when its first plan is the original finite edge family. -/
theorem original_pathWeakSlabReadout_eq_finite_flux
    {I : Type*} [Fintype I] (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (edges : I → LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (hplan : (scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) =
      ∑ i, Measure.dirac (edges i))
    (φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (s t : ℝ) :
    originalSeedPathWeakSlabReadout S w φ s t scene =
      originalCompletePathSlabFlux S w edges φ s t := by
  unfold originalSeedPathWeakSlabReadout
  rw [integral_physicalPairKernel_eq_finite_sum scene edges hplan]
  rfl

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The same actual weighted law supplies joint clock/scene L1 of the current
from its genuine complete-path first moment, without any L2/traffic callback. -/
theorem integrable_original_pathClockWindowReadout_prod
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hηI : Integrable η volume) :
    Integrable (fun z : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × ℝ ↦
      legalMarkedPathWindowReadout (finrank ℝ S.covector.ker)
        (originalSeedPathOffset S w z.2) η (originalSeedClockOccupation S w z.2) z.1)
      ((Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).prod volume) := by
  have hm := stronglyMeasurable_original_pathClockWindowReadout_joint S hF hw hη
  refine ⟨hm.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_norm]
  rw [lintegral_prod _ hm.measurable.norm.ennreal_ofReal.aemeasurable]
  apply lt_of_le_of_lt (lintegral_mono (fun scene ↦
    lintegral_original_pathClockWindowReadout_norm_le_traffic S hF hw hη scene))
  exact D.lintegral_original_completePathAbsoluteTraffic_lt_top hF hw hbounds Q hη.abs hηI.abs

/-- Every deterministic clock restriction of the actual current is integrable
under the SAME weighted matching law, from its full original traffic first moment. -/
theorem integrable_original_pathClockSetCurrent
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hηI : Integrable η volume) (A : Set ℝ) :
    Integrable (originalSeedPathClockSetCurrent S w η A)
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
  have hjoint := D.integrable_original_pathClockWindowReadout_prod hF hw hbounds Q hη hηI
  exact (hjoint.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)).integral_prod_left

/-- Actual endpoint first variation and path-position Campbell readout center
every deterministic clock-set current under the same attained minimizer. -/
theorem integral_original_pathClockSetCurrent_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (τ : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ R.value τ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hηI : Integrable η volume) (A : Set ℝ) :
    (∫ scene, originalSeedPathClockSetCurrent S w η A scene
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) = 0 := by
  have hjoint := (D.integrable_original_pathClockWindowReadout_prod hF hw hbounds Q hη hηI).mono_measure (Measure.prod_mono le_rfl (Measure.restrict_le_self (s := A)))
  change (∫ scene, ∫ c in A, legalMarkedPathWindowReadout (finrank ℝ S.covector.ker)
    (originalSeedPathOffset S w c) η (originalSeedClockOccupation S w c) scene ∂volume
    ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) = 0
  rw [integral_integral_swap hjoint]
  have hpoint (c : ℝ) : (∫ scene, legalMarkedPathWindowReadout (finrank ℝ S.covector.ker)
      (originalSeedPathOffset S w c) η (originalSeedClockOccupation S w c) scene
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) = 0 := by
    rw [(Q.pathWindowReadout_integrable_and_integral (originalSeedPathOffset S w c)
      (measurable_originalSeedPathOffset S hF hw c) hηI
      (D.integrable_original_clockOccupation hF hw hgap hbounds Q c)).2,
      D.integral_original_clockOccupation_eq_zero_of_minimal_value hF hw hgap hbounds Q τ hmin c]
    simp
  simp_rw [hpoint]
  exact integral_zero _ _

/-- Conditioning on any genuine invariant event preserves the attained
minimum, so its original deterministic clock-set current has zero conditional
vector mean. Joint L1 is produced internally, not postulated. -/
theorem condExp_original_pathClockSetCurrent_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 0 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (τ : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ R.value τ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hηI : Integrable η volume) (A : Set ℝ) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))[
      originalSeedPathClockSetCurrent S w η A | Q.invariantSigma] =ᵐ[(Q.law : Measure _)]
        fun _ ↦ 0 := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  apply condExp_eq_zero_of_all_positive_cond_integral_eq_zero _
    (aeInvariantEventSigma_le _ _)
    (D.integrable_original_pathClockSetCurrent hF hw hbounds Q hη hηI A)
  intro B hB hpos
  exact D.integral_original_pathClockSetCurrent_eq_zero_of_minimal_value hF hw hgap hbounds
    (Q.invariantConditionedMatching hq B hB.1 hpos hB.2) τ
    (Q.invariantConditionedMatching_minimal hq τ hmin B hB.1 hpos hB.2) hη hηI A

/-- Every fixed prefix of the actual path-position unit-window current is
centered conditionally on the same original scene's invariant sigma algebra. -/
theorem condExp_original_pathPrefixCurrent_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 0 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (τ : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ R.value τ) (t : ℝ) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))[
      originalSeedPathPrefixCurrent S w t | Q.invariantSigma] =ᵐ[(Q.law : Measure _)]
        fun _ ↦ 0 := by
  exact D.condExp_original_pathClockSetCurrent_eq_zero_of_minimal_value
    hF hw hq hgap hbounds Q τ hmin
    (measurable_const.indicator (measurableSet_palmUnitCube _))
    (integrable_legalMarkedUnitWindowWeight _) (Iic t)

/-- Every fixed slab of the actual path-position unit-window current is
centered under the same invariant conditioning and unchanged minimizing law. -/
theorem condExp_original_pathSlabCurrent_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 0 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (τ : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ R.value τ) (s t : ℝ) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))[
      originalSeedPathSlabCurrent S w s t | Q.invariantSigma] =ᵐ[(Q.law : Measure _)]
        fun _ ↦ 0 := by
  exact D.condExp_original_pathClockSetCurrent_eq_zero_of_minimal_value
    hF hw hq hgap hbounds Q τ hmin
    (measurable_const.indicator (measurableSet_palmUnitCube _))
    (integrable_legalMarkedUnitWindowWeight _) (Ioc s t)

/-- The same actual finite first plan has the original nonnegative cut/slab
charges in its weak divergence, with no cube filter on its physical endpoints. -/
theorem original_pathWeakSlabReadout_divergence_balance
    {I : Type*} [Fintype I]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (edges : I → LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (hplan : (scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) =
      ∑ i, Measure.dirac (edges i))
    (ha : ∀ i, (edges i).1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : ∀ i, (edges i).2.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hab : ∀ i, (edges i).1.2 < (edges i).2.2)
    {s t : ℝ} (hst : s ≤ t) {φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) :
    -originalSeedPathWeakSlabReadout S w φ s t scene =
      (∫ x, φ x ∂originalCompletePathSlabSources edges s t) -
      (∫ x, φ x ∂originalCompletePathSlabTargets edges s t) +
      (∫ x, φ x ∂originalCompletePathActiveCut S w edges s) -
        ∫ x, φ x ∂originalCompletePathActiveCut S w edges t := by
  rw [original_pathWeakSlabReadout_eq_finite_flux S w scene edges hplan]
  exact D.original_complete_path_slab_divergence_balance hF hw edges ha hb hab hst hφ

/-- The original existence theorem produces ONE attained weighted minimizer
whose every deterministic prefix and slab current is invariant-conditionally
centered. Neither a completed traffic estimate nor centering is an input. -/
theorem exists_original_minimizer_prefix_slab_currents_centered
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (hgc : ContinuousOn (Function.uncurry g)
      {p | p.1 - S.level ∈ Ioo D.lo D.hi ∧
        p.2 - S.level ∈ Ioo D.lo D.hi ∧ p.1 < p.2}) (τ : ℝ) :
    ∃ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g,
      Q.value τ = D.originalWeightedStationaryInf gap g τ ∧
      (∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g, Q.value τ ≤ R.value τ) ∧
      (∀ t : ℝ, (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))[
        originalSeedPathPrefixCurrent S w t | Q.invariantSigma] =ᵐ[(Q.law : Measure _)]
          fun _ ↦ 0) ∧
      ∀ s t : ℝ, (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))[
        originalSeedPathSlabCurrent S w s t | Q.invariantSigma] =ᵐ[(Q.law : Measure _)]
          fun _ ↦ 0 := by
  obtain ⟨Q,heq,hmin⟩ := D.exists_original_weighted_stationary_minimizer
    hF hw hq hgap hbounds π hπ horder hg hgb hgc τ
  exact ⟨Q,heq,hmin,
    fun t ↦ D.condExp_original_pathPrefixCurrent_eq_zero_of_minimal_value
      hF hw (by omega) hgap hbounds Q τ hmin t,
    fun s t ↦ D.condExp_original_pathSlabCurrent_eq_zero_of_minimal_value
      hF hw (by omega) hgap hbounds Q τ hmin s t⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction

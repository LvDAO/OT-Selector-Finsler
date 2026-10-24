import OTSelector.Reconstruction.MarkedStationaryValuePhysicalPairAnchorReadout

/-!
# The actual true Palm clock gap controls whole original scene support

Stationary Campbell factorization transfers null bad-clock Palm mass to the
whole original first edge measure. The positive-gap condition is closed, so
it holds on every actual support edge rather than only almost every edge.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalTruePalmClockGapInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalTruePalmClockGapPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- A gap in the same actual true probability Palm is respected by every
support edge of the same actual stationary scene, with no proper projection
or finite unweighted displacement moment. -/
theorem ae_support_clockGap_of_stationary_truePalm_gap
    {q : ℕ} (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hstat : ∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q)) (Q : Measure (LegalMarkedOptimalInputScene q)))
    (hprob : IsProbabilityMeasure (legalMarkedJointPalm q Q)) {δ : ℝ}
    (hgap : ∀ᵐ m ∂legalMarkedJointPalm q Q, δ ≤ m.1.2 - m.1.1) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
        δ ≤ e.2.2 - e.1.2 := by
  let _ := hprob
  let P := legalMarkedInputPairLaw q Q
  have hunit : (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)}
      ∂(P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) < ∞ := by
    rw [← physicalScenePairCampbell_unitCube, ← cubePalm_apply (Fin q) _ MeasurableSet.univ]
    change legalMarkedJointPalm q Q univ < ∞
    rw [measure_univ]
    exact ENNReal.one_lt_top
  have hcamp := physicalScenePairCampbell_eq_volume_prod_cubePalm
    (P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
    (measurePreserving_legalMarkedInputPairLaw q Q hstat) hunit
  let B : Set (PhysicalPairPalmMark (Fin q)) := {m | ¬ δ ≤ m.1.2 - m.1.1}
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const (measurable_fst.snd.sub measurable_fst.fst)).compl
  have : IsProbabilityMeasure (cubePalm (Fin q) (physicalScenePairCampbell
      (P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))) := hprob
  have hzero : physicalScenePairCampbell (P : Measure
      (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) (univ ×ˢ B) = 0 := by
    rw [hcamp, Measure.prod_prod]
    change volume univ * legalMarkedJointPalm q Q B = 0
    rw [ae_iff.mp hgap, mul_zero]
  rw [physicalScenePairCampbell, Measure.bind_apply (MeasurableSet.univ.prod hB)
    (Kernel.measurable _).aemeasurable] at hzero
  have hpair := (lintegral_eq_zero_iff (Kernel.measurable_coe physicalScenePairKernel
    (MeasurableSet.univ.prod hB))).mp hzero
  have hpaired : ∀ᵐ scene ∂(P : Measure
      (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))),
      ∀ᵐ e ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q)), δ ≤ e.2.2 - e.1.2 := by
    filter_upwards [hpair] with scene hs
    apply ae_iff.mpr
    rw [physicalScenePairKernel_apply, Measure.map_apply measurable_physicalPairAnchor
      (MeasurableSet.univ.prod hB)] at hs
    change (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      (physicalPairAnchor ⁻¹' (univ ×ˢ B)) = 0 at hs
    convert hs using 1
    congr 1
    ext e
    simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_ofPred_eq, B,
      physicalPairAnchor]
  have hjoint : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)), δ ≤ e.2.2 - e.1.2 :=
    ae_of_ae_map measurable_fst.aemeasurable hpaired
  filter_upwards [hjoint] with s hs
  exact Measure.support_subset_of_isClosed
    (isClosed_le continuous_const (continuous_snd.snd.sub continuous_fst.snd)) hs

end OTSelector.Reconstruction

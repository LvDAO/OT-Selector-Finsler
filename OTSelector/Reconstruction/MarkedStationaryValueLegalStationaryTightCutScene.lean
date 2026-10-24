import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryTightCut
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputFiniteMatching

/-!
# Tight original clock cuts separate the entire actual integer matching

The original probability Palm supplies the finite unit-window moment needed
for Campbell factorization. Zero tight-cut Palm mass then gives zero whole
scene crossing mass. Actual integer atoms exclude every crossing support edge,
so scalar block separation requires no additional matching hypothesis.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalStationaryTightCutSceneInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryTightCutScenePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- A genuine original matching produces its exact full Campbell factor from
its own probability Palm; no unit-moment hypothesis is supplied. -/
theorem LegalWeightedStationaryPoissonMatching.campbell_eq_volume_prod_palm
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    physicalScenePairCampbell (legalMarkedInputPairLaw q M.law :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (volume : Measure (Fin q → ℝ)).prod (legalMarkedJointPalm q M.law) := by
  let P := legalMarkedInputPairLaw q M.law
  have : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  have hunit : (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)}
      ∂(P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) < ∞ := by
    rw [← physicalScenePairCampbell_unitCube, ← cubePalm_apply (Fin q) _ MeasurableSet.univ]
    change legalMarkedJointPalm q M.law univ < ∞
    rw [measure_univ]
    norm_num
  exact physicalScenePairCampbell_eq_volume_prod_cubePalm _
    (measurePreserving_legalMarkedInputPairLaw q M.law M.stationary) hunit

/-- A tight original prefix cut is respected by every actual integer support
edge in almost every entire original stationary scene. -/
theorem LegalWeightedStationaryPoissonMatching.ae_support_no_crossing_of_tight_cut
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (c : ℝ) (hcut : α (Iic c) = β (Iic c)) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
        ¬ (e.1.2 ≤ c ∧ c < e.2.2) := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let B : Set (PhysicalPairPalmMark (Fin q)) := {m | m.1.1 ≤ c ∧ c < m.1.2}
  let E : Set (LegalMarkedPhysicalEdge q) := {e | e.1.2 ≤ c ∧ c < e.2.2}
  have hB : MeasurableSet B := (measurableSet_le measurable_fst.fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_fst.snd)
  have hEB : physicalPairAnchor ⁻¹' (univ ×ˢ B) = E := by
    ext e
    simp only [B, E, mem_preimage, mem_prod, mem_univ, true_and, mem_ofPred_eq, physicalPairAnchor]
  have hzero : physicalScenePairCampbell (legalMarkedInputPairLaw q M.law :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
      (univ ×ˢ B) = 0 := by
    rw [M.campbell_eq_volume_prod_palm, Measure.prod_prod, M.palm_crossing_eq_zero_of_tight c hcut,
      mul_zero]
  rw [physicalScenePairCampbell, Measure.bind_apply (MeasurableSet.univ.prod hB)
    (Kernel.measurable _).aemeasurable] at hzero
  have hpair := (lintegral_eq_zero_iff (Kernel.measurable_coe physicalScenePairKernel
    (MeasurableSet.univ.prod hB))).mp hzero
  have hp : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) E = 0 := by
    have h : ∀ᵐ scene ∂(legalMarkedInputPairLaw q M.law :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))),
        (scene.1 : Measure (LegalMarkedPhysicalEdge q)) E = 0 := by
      filter_upwards [hpair] with scene hs
      simpa only [physicalScenePairKernel_apply, Measure.map_apply measurable_physicalPairAnchor
        (MeasurableSet.univ.prod hB), hEB, Pi.zero_apply] using hs
    exact ae_of_ae_map measurable_fst.aemeasurable h
  filter_upwards [hp, M.full_matching] with s hs hm
  intro e he hcross
  have hc := ((isLegalSimpleCountingMeasure_iff (0 : LegalMarkedPhysicalEdge q) s.1.1).mp
    hm.simple_edges).1
  have hmass := one_le_singleton_of_mem_support_of_legalCounting (0 : LegalMarkedPhysicalEdge q)
    s.1.1 hc he
  have hn : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) {e} = 0 :=
    measure_mono_null (singleton_subset_iff.mpr hcross) hs
  rw [hn] at hmass
  norm_num at hmass

/-- Any original countable family of tight scalar cuts separates all actual
support edges on one common event of full scene probability. -/
theorem LegalWeightedStationaryPoissonMatching.ae_support_no_crossing_tight_cuts
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {J : Type*} [Countable J] (c : J → ℝ) (hcut : ∀ j, α (Iic (c j)) = β (Iic (c j))) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)), ∀ j,
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
        ¬ (e.1.2 ≤ c j ∧ c j < e.2.2) := by
  exact ae_all_iff.mpr (fun j ↦ M.ae_support_no_crossing_of_tight_cut (c j) (hcut j))

end OTSelector.Reconstruction

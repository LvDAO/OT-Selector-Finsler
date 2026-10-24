import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryDilation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import OTSelector.MeasureTheory.HomogeneousMeasureReadout

/-!
# Exact Campbell transport under physical dilation

The original scene, both original clocks and the full displacement remain in
the same joint object. Dilation transports its actual Campbell measure, rather
than postulating a new matching law at the desired intensity.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local instance markedStationaryValueLegalStationaryDilationPalmInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryDilationPalmPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Actual clocks are fixed and the full original displacement is dilated. -/
def legalPairMarkDilation (q : ℕ) (c : ℝ)
    (m : PhysicalPairPalmMark (Fin q)) : PhysicalPairPalmMark (Fin q) := (m.1, c • m.2)

theorem measurable_legalPairMarkDilation (q : ℕ) (c : ℝ) :
    Measurable (legalPairMarkDilation q c) := measurable_fst.prodMk (measurable_snd.const_smul c)

/-- The source anchor and displacement undergo the same original dilation. -/
def legalPairAnchorDilation (q : ℕ) (c : ℝ)
    (p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) :
    (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) := (c • p.1, legalPairMarkDilation q c p.2)

theorem measurable_legalPairAnchorDilation (q : ℕ) (c : ℝ) :
    Measurable (legalPairAnchorDilation q c) :=
  (measurable_fst.const_smul c).prodMk ((measurable_legalPairMarkDilation q c).comp measurable_snd)

/-- Exact covariance uses every original edge, with no target truncation. -/
theorem physicalPairAnchor_legalMarkedEdgeDilation (q : ℕ) (c : ℝ) (hc : c ≠ 0)
    (e : LegalMarkedPhysicalEdge q) :
    physicalPairAnchor (legalMarkedEdgeDilation q c hc e) =
      legalPairAnchorDilation q c (physicalPairAnchor e) := by
  change (c • e.1.1, ((e.1.2, e.2.2), c • e.2.1 - c • e.1.1)) =
    (c • e.1.1, ((e.1.2, e.2.2), c • (e.2.1 - e.1.1)))
  rw [smul_sub]

/-- The Campbell measure of the same original joint scene is transported by
its actual source/displacement dilation map. -/
theorem physicalScenePairCampbell_dilated_legalInputLaw (q : ℕ)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) (c : ℝ) (hc : c ≠ 0) :
    physicalScenePairCampbell (legalMarkedInputPairLaw q
      (Q.map (continuous_legalMarkedInputSceneDilation q c hc).measurable.aemeasurable) :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))).map
          (legalPairAnchorDilation q c) := by
  apply Measure.ext
  intro B hB
  have hpre : MeasurableSet (legalPairAnchorDilation q c ⁻¹' B) :=
    hB.preimage (measurable_legalPairAnchorDilation q c)
  rw [Measure.map_apply (measurable_legalPairAnchorDilation q c) hB]
  simp only [physicalScenePairCampbell, Measure.bind_apply hB
    (Kernel.measurable _).aemeasurable, Measure.bind_apply hpre (Kernel.measurable _).aemeasurable]
  change (∫⁻ scene, physicalScenePairKernel scene B
      ∂((Q : Measure (LegalMarkedOptimalInputScene q)).map
        (legalMarkedInputSceneDilation q c hc)).map Prod.fst) =
    ∫⁻ scene, physicalScenePairKernel scene (legalPairAnchorDilation q c ⁻¹' B)
      ∂(Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst
  rw [lintegral_map (Kernel.measurable_coe _ hB) measurable_fst,
    lintegral_map (Kernel.measurable_coe _ hpre) measurable_fst]
  have hBjoint : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      physicalScenePairKernel s.1 B) := (Kernel.measurable_coe _ hB).comp measurable_fst
  have hchange := lintegral_map (μ := (Q : Measure (LegalMarkedOptimalInputScene q))) hBjoint
    (continuous_legalMarkedInputSceneDilation q c hc).measurable
  rw [hchange]
  apply lintegral_congr_ae
  filter_upwards with s
  rw [physicalScenePairKernel_apply, physicalScenePairKernel_apply]
  change (((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map
      (legalMarkedEdgeDilation q c hc)).map physicalPairAnchor) B =
    ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map physicalPairAnchor)
      (legalPairAnchorDilation q c ⁻¹' B)
  rw [Measure.map_map measurable_physicalPairAnchor
      (legalMarkedEdgeDilation q c hc).continuous.measurable,
    Measure.map_apply measurable_physicalPairAnchor hpre,
    Measure.map_apply (measurable_physicalPairAnchor.comp
      (legalMarkedEdgeDilation q c hc).continuous.measurable) hB]
  congr 1
  ext e
  simp only [mem_preimage, Function.comp_def, physicalPairAnchor_legalMarkedEdgeDilation]

/-- Dilation produces the exact unnormalized original Palm: its intensity
is the Haar Jacobian and its paired marks retain the entire scaled displacement. -/
theorem legalMarkedJointPalm_dilated_of_weighted_stationary
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (c : ℝ) (hc : c ≠ 0) :
    legalMarkedJointPalm q
      (M.law.map (continuous_legalMarkedInputSceneDilation q c hc).measurable.aemeasurable) =
      ENNReal.ofReal |(c ^ q)⁻¹| •
        (legalMarkedJointPalm q M.law).map (legalPairMarkDilation q c) := by
  let P := legalMarkedInputPairLaw q M.law
  let η := legalMarkedJointPalm q M.law
  have : IsProbabilityMeasure η := M.palm_probability
  have hunit : (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)} ∂(P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) < ∞ := by
    rw [← physicalScenePairCampbell_unitCube]
    rw [← cubePalm_apply (Fin q) _ MeasurableSet.univ]
    change η univ < ∞
    rw [measure_univ]
    norm_num
  have hcamp : physicalScenePairCampbell (P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (volume : Measure (Fin q → ℝ)).prod η :=
    physicalScenePairCampbell_eq_volume_prod_cubePalm _
      (measurePreserving_legalMarkedInputPairLaw q M.law M.stationary) hunit
  have hvol : (volume : Measure (Fin q → ℝ)).map (fun x ↦ c • x) =
      ENNReal.ofReal |(c ^ q)⁻¹| • (volume : Measure (Fin q → ℝ)) := by
    simpa using Measure.map_addHaar_smul (volume : Measure (Fin q → ℝ)) hc
  have hnew : physicalScenePairCampbell (legalMarkedInputPairLaw q
      (M.law.map (continuous_legalMarkedInputSceneDilation q c hc).measurable.aemeasurable) :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      ENNReal.ofReal |(c ^ q)⁻¹| •
        ((volume : Measure (Fin q → ℝ)).prod (η.map (legalPairMarkDilation q c))) := by
    rw [physicalScenePairCampbell_dilated_legalInputLaw, hcamp]
    change ((volume : Measure (Fin q → ℝ)).prod η).map
      (Prod.map (fun x ↦ c • x) (legalPairMarkDilation q c)) = _
    calc
      _ = ((volume : Measure (Fin q → ℝ)).map (fun x ↦ c • x)).prod
          (η.map (legalPairMarkDilation q c)) :=
        (Measure.map_prod_map _ _ (measurable_id.const_smul c)
          (measurable_legalPairMarkDilation q c)).symm
      _ = _ := by rw [hvol, Measure.prod_smul_left]
  apply Measure.ext
  intro B hB
  change cubePalm (Fin q) _ B = (ENNReal.ofReal |(c ^ q)⁻¹| • η.map (legalPairMarkDilation q c)) B
  rw [cubePalm_apply (Fin q) _ hB, hnew, Measure.smul_apply, Measure.prod_prod,
    volume_palmUnitCube, one_mul, Measure.smul_apply]

/-- The actual homogeneous kinetic readout has the exact intensity-times-
quadratic scaling under the same physical dilation. -/
theorem integral_kinetic_dilated_legalMarkedJointPalm
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (c : ℝ) (hc : c ≠ 0)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hhom : ∀ a b v, kin a b (c • v) = c ^ 2 * kin a b v) :
    (∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q
      (M.law.map (continuous_legalMarkedInputSceneDilation q c hc).measurable.aemeasurable)) =
      |(c ^ q)⁻¹| * c ^ 2 * ∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q M.law := by
  rw [legalMarkedJointPalm_dilated_of_weighted_stationary M c hc]
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using
    integral_smul_map_of_comp_eq_mul (legalMarkedJointPalm q M.law)
      (legalPairMarkDilation q c) (measurable_legalPairMarkDilation q c)
      (ENNReal.ofReal |(c ^ q)⁻¹|)
      (fun m : PhysicalPairPalmMark (Fin q) ↦ kin m.1.1 m.1.2 m.2) hk (c ^ 2)
      (fun m ↦ hhom m.1.1 m.1.2 m.2)

/-- The original paired-clock probe is fixed by spatial dilation and scales
only by the actual change in physical source intensity. -/
theorem integral_probe_dilated_legalMarkedJointPalm
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (c : ℝ) (hc : c ≠ 0)
    (hg : Measurable (Function.uncurry g)) :
    (∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q
      (M.law.map (continuous_legalMarkedInputSceneDilation q c hc).measurable.aemeasurable)) =
      |(c ^ q)⁻¹| * ∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q M.law := by
  rw [legalMarkedJointPalm_dilated_of_weighted_stationary M c hc]
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _),mul_one] using
    integral_smul_map_of_comp_eq_mul (legalMarkedJointPalm q M.law)
      (legalPairMarkDilation q c) (measurable_legalPairMarkDilation q c)
      (ENNReal.ofReal |(c ^ q)⁻¹|)
      (fun m : PhysicalPairPalmMark (Fin q) ↦ g m.1.1 m.1.2)
      (hg.comp measurable_fst) 1 (fun m ↦ (one_mul _).symm)

end OTSelector.Reconstruction

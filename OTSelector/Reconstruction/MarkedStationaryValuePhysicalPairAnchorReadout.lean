import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryTightCutScene
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Compact actual edge tests read the full paired-mark Palm

The physical source anchor, both original clocks, and the full displacement
form a homeomorphic coordinate system on the entire marked edge. Compact
product tests therefore give genuine compact edge tests. Their actual same-law
expectations factor through the stationary Campbell measure and its true Palm.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
local instance physicalPairAnchorReadoutInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance physicalPairAnchorReadoutPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Actual edge coordinates are equivalent to source position, original
paired clocks and full displacement, with no lost geometric information. -/
def physicalPairAnchorHomeomorph (q : ℕ) :
    LegalMarkedPhysicalEdge q ≃ₜ ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) where
  toFun := physicalPairAnchor
  invFun p := ((p.1, p.2.1.1), (p.1 + p.2.2, p.2.1.2))
  left_inv e := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change e.1.1 + (e.2.1 - e.1.1) = e.2.1
        abel
      · rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · change p.1 + p.2.2 - p.1 = p.2.2
        abel
  continuous_toFun := by
    unfold physicalPairAnchor
    fun_prop
  continuous_invFun := by fun_prop

/-- A compact source-position test and compact complete-mark test give a
compact test of the original unaltered edge through the anchor homeomorphism. -/
def physicalAnchoredProductTest (q : ℕ) (h : C_c(Fin q → ℝ, ℝ))
    (f : C_c(PhysicalPairPalmMark (Fin q), ℝ)) : C_c(LegalMarkedPhysicalEdge q, ℝ) :=
  (cavityProductTest h f).comp (physicalPairAnchorHomeomorph q).toCocompactMap

@[simp]
theorem physicalAnchoredProductTest_apply (q : ℕ) (h : C_c(Fin q → ℝ, ℝ))
    (f : C_c(PhysicalPairPalmMark (Fin q), ℝ)) (e : LegalMarkedPhysicalEdge q) :
    physicalAnchoredProductTest q h f e =
      h e.1.1 * f ((e.1.2, e.2.2), e.2.1 - e.1.1) := rfl

/-- The actual local edge readout is exactly the compact product readout
under the same actual edge's anchor pushforward. -/
theorem testIntegral_physicalAnchoredProductTest_eq_anchor (q : ℕ)
    (π : LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) (h : C_c(Fin q → ℝ, ℝ))
    (f : C_c(PhysicalPairPalmMark (Fin q), ℝ)) :
    LocalFiniteMeasure.testIntegral π (physicalAnchoredProductTest q h f) =
      ∫ p, cavityProductTest h f p ∂(π : Measure (LegalMarkedPhysicalEdge q)).map physicalPairAnchor := by
  change (∫ e, cavityProductTest h f (physicalPairAnchor e)
    ∂(π : Measure (LegalMarkedPhysicalEdge q))) = _
  exact (integral_map (μ := (π : Measure (LegalMarkedPhysicalEdge q)))
    (f := fun p ↦ cavityProductTest h f p) measurable_physicalPairAnchor.aemeasurable
    (show AEStronglyMeasurable (fun p ↦ cavityProductTest h f p)
      ((π : Measure (LegalMarkedPhysicalEdge q)).map physicalPairAnchor) from
      (cavityProductTest h f).continuous.aestronglyMeasurable)).symm

/-- The original scene's actual first-edge kernel gives precisely the same
compact edge test, with no change of plan or Palm normalization. -/
theorem integral_physicalScenePairKernel_anchoredProduct (q : ℕ)
    (s : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))
    (h : C_c(Fin q → ℝ, ℝ)) (f : C_c(PhysicalPairPalmMark (Fin q), ℝ)) :
    (∫ p, cavityProductTest h f p ∂physicalScenePairKernel s) =
      LocalFiniteMeasure.testIntegral s.1 (physicalAnchoredProductTest q h f) := by
  rw [physicalScenePairKernel_apply]
  exact (testIntegral_physicalAnchoredProductTest_eq_anchor q s.1 h f).symm

/-- Kernel Fubini on the actual measure bind, retaining its original
probability sample and all original matching/input correlations. -/
theorem integral_bind_kernel_eq_integral_integral
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (κ : Kernel X Y) {f : Y → ℝ}
    (hi : Integrable f (P.bind κ)) :
    (∫ y, f y ∂P.bind κ) = ∫ x, ∫ y, f y ∂κ x ∂P := by
  change Integrable f (κ ∘ₘ P) at hi
  rw [Measure.comp_eq_comp_const_apply] at hi
  have ht := ProbabilityTheory.Kernel.integral_comp hi
  simpa only [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply] using ht

/-- The true paired-mark Palm has exactly the original first matching's
actual expected source-unit-window mass, on every joint scene law. -/
theorem legalMarkedJointPalm_univ_eq_expected_sourceUnitMass (q : ℕ)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    legalMarkedJointPalm q Q univ =
      ∫⁻ s, (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
        {e | e.1.1 ∈ palmUnitCube (Fin q)}
        ∂(Q : Measure (LegalMarkedOptimalInputScene q)) := by
  rw [legalMarkedJointPalm, cubePalm_apply (Fin q) _ MeasurableSet.univ,
    physicalScenePairCampbell_unitCube]
  have hm : Measurable (fun s :
      CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ↦
      (s.1 : Measure (LegalMarkedPhysicalEdge q)) {e | e.1.1 ∈ palmUnitCube (Fin q)}) :=
    (Measure.measurable_coe ((measurableSet_palmUnitCube (Fin q)).preimage
      measurable_fst.fst)).comp (measurable_localFiniteMeasure_coe.comp measurable_fst)
  change (∫⁻ s, (s.1 : Measure (LegalMarkedPhysicalEdge q))
    {e | e.1.1 ∈ palmUnitCube (Fin q)}
    ∂(Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst) = _
  exact lintegral_map hm measurable_fst

/-- Every stationary actual joint scene with finite true source-unit-window
mass has the compact original edge readout of its own finite true Palm. No
fullness, simple-input, prescribed-intensity or kinetic assumption is needed. -/
theorem integral_physicalAnchoredProductTest_of_stationary
    {q : ℕ} (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hstat : ∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q))
      (Q : Measure (LegalMarkedOptimalInputScene q)))
    (hunit : (∫⁻ s, (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)}
      ∂(Q : Measure (LegalMarkedOptimalInputScene q))) < ∞)
    (h : C_c(Fin q → ℝ, ℝ)) (f : C_c(PhysicalPairPalmMark (Fin q), ℝ)) :
    (∫ s, LocalFiniteMeasure.testIntegral s.1.1 (physicalAnchoredProductTest q h f)
      ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
      (∫ x, h x ∂(volume : Measure (Fin q → ℝ))) *
        ∫ m, f m ∂legalMarkedJointPalm q Q := by
  have hpalm : legalMarkedJointPalm q Q univ < ∞ := by
    rw [legalMarkedJointPalm_univ_eq_expected_sourceUnitMass]
    exact hunit
  have : IsFiniteMeasure (legalMarkedJointPalm q Q) := ⟨hpalm⟩
  have hunitP : (∫⁻ s, (s.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)}
      ∂(legalMarkedInputPairLaw q Q :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) < ∞ := by
    rw [← physicalScenePairCampbell_unitCube, ← cubePalm_apply (Fin q) _ MeasurableSet.univ]
    exact hpalm
  have hcamp := physicalScenePairCampbell_eq_volume_prod_cubePalm
    (legalMarkedInputPairLaw q Q :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
    (measurePreserving_legalMarkedInputPairLaw q Q hstat) hunitP
  change physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
    (volume : Measure (Fin q → ℝ)).prod (legalMarkedJointPalm q Q) at hcamp
  let P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)) :=
    legalMarkedInputPairLaw q Q
  let G := cavityProductTest h f
  have hi : Integrable G (physicalScenePairCampbell P) := by
    rw [hcamp]
    exact G.integrable
  have ht := integral_bind_kernel_eq_integral_integral P physicalScenePairKernel hi
  change (∫ p, G p ∂physicalScenePairCampbell P) = _ at ht
  change (∫ p, cavityProductTest h f p ∂physicalScenePairCampbell P) =
    ∫ s, ∫ p, cavityProductTest h f p ∂physicalScenePairKernel s ∂P at ht
  simp_rw [integral_physicalScenePairKernel_anchoredProduct q _ h f] at ht
  rw [hcamp] at ht
  have hprod : (∫ p, cavityProductTest h f p ∂(volume : Measure (Fin q → ℝ)).prod
      (legalMarkedJointPalm q Q)) =
      (∫ x, h x ∂(volume : Measure (Fin q → ℝ))) *
        ∫ m, f m ∂legalMarkedJointPalm q Q := by
    exact integral_prod_mul h f
  rw [hprod] at ht
  have ht' := ht.symm
  change (∫ s, LocalFiniteMeasure.testIntegral s.1
      (physicalAnchoredProductTest q h f)
      ∂(Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst) = _ at ht'
  have hmap : (∫ s : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q),
      LocalFiniteMeasure.testIntegral s.1 (physicalAnchoredProductTest q h f)
      ∂(Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst) =
      ∫ s, LocalFiniteMeasure.testIntegral s.1.1 (physicalAnchoredProductTest q h f)
        ∂(Q : Measure (LegalMarkedOptimalInputScene q)) :=
    integral_map (f := fun s : CavityLocalScene (LegalMarkedPhysicalPoint q)
      (LegalMarkedPhysicalPoint q) ↦
        LocalFiniteMeasure.testIntegral s.1 (physicalAnchoredProductTest q h f))
      measurable_fst.aemeasurable
      (show AEStronglyMeasurable
        (fun s : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ↦
          LocalFiniteMeasure.testIntegral s.1 (physicalAnchoredProductTest q h f)) _ from
        ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst).aestronglyMeasurable)
  exact hmap.symm.trans ht'

/-- Every genuine matching has the exact expected compact original edge
readout prescribed by its own true paired-clock/full-displacement Palm. -/
theorem LegalWeightedStationaryPoissonMatching.integral_physicalAnchoredProductTest
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (h : C_c(Fin q → ℝ, ℝ)) (f : C_c(PhysicalPairPalmMark (Fin q), ℝ)) :
    (∫ s, LocalFiniteMeasure.testIntegral s.1.1 (physicalAnchoredProductTest q h f)
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
      (∫ x, h x ∂(volume : Measure (Fin q → ℝ))) *
        ∫ m, f m ∂legalMarkedJointPalm q M.law := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  apply integral_physicalAnchoredProductTest_of_stationary M.law M.stationary ?_ h f
  rw [← legalMarkedJointPalm_univ_eq_expected_sourceUnitMass, measure_univ]
  norm_num

end OTSelector.Reconstruction

import OTSelector.Reconstruction.FinslerPhysicalSceneMacroProbeConvolution
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Literal unit-grid root domains at the original scale

Each half-open grid box has the original required Haar volume. Compact
macroscopic supports are covered by finitely many of these original root laws.
-/
open Set Function MeasureTheory BoxIntegral OTSelector.Probability
open scoped ENNReal Topology CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/-- A literal half-open unit box viewed at the original microscopic scale. -/
def physicalSceneRootGridDomain (scale : ℝ) (ν : ι → ℤ) : Set (ι → ℝ) :=
  (fun z ↦ scale⁻¹ • z) ⁻¹' (unitPartition.box 1 ν : Set (ι → ℝ))

/-- Every actual unit-grid root domain is measurable. -/
theorem measurableSet_physicalSceneRootGridDomain (scale : ℝ) (ν : ι → ℤ) :
    MeasurableSet (physicalSceneRootGridDomain scale ν) :=
  (unitPartition.box 1 ν).measurableSet_coe.preimage (measurable_const_smul _)

/-- Its actual Haar volume is the original scale to the spatial dimension,
independently of the integer box index. -/
theorem volume_physicalSceneRootGridDomain (scale : ℝ) (hscale : 0 < scale) (ν : ι → ℤ) :
    volume (physicalSceneRootGridDomain scale ν) = ENNReal.ofReal (scale ^ Fintype.card ι) := by
  rw [physicalSceneRootGridDomain, Measure.addHaar_preimage_smul volume (inv_ne_zero hscale.ne'),
    unitPartition.volume_box]
  simp [inv_pow, abs_of_pos (pow_pos hscale _)]

omit [Fintype ι] in
/-- Distinct original root boxes are disjoint before any plan is observed. -/
theorem pairwise_disjoint_physicalSceneRootGridDomain (scale : ℝ) :
    Pairwise (Disjoint on (physicalSceneRootGridDomain (ι := ι) scale)) := by
  intro ν ν' hν
  exact (unitPartition.disjoint.mp hν).preimage _

/-- A bounded macroscopic set is covered by a finite collection of literal
unit-grid boxes. No normalization of the population base coordinates is assumed. -/
theorem exists_finite_unit_root_grid_cover {K : Set (ι → ℝ)} (hK : Bornology.IsBounded K) :
    ∃ cells : Finset (ι → ℤ), K ⊆ ⋃ ν ∈ cells, (unitPartition.box 1 ν : Set (ι → ℝ)) := by
  obtain ⟨B, hB, hKB⟩ := BoxIntegral.le_hasIntegralVertices_of_isBounded hK
  refine ⟨unitPartition.admissibleIndex 1 B, ?_⟩
  intro x hx
  exact mem_biUnion (unitPartition.mem_admissibleIndex_of_mem_box 1 hB (hKB hx))
    (unitPartition.mem_box_iff_index.mpr rfl)

omit [Fintype ι] in
/-- The original root boxes' macroscopic coordinates stay in a genuine
compact box, as required for the original joint scene compactness theorem. -/
theorem physicalSceneRootGridDomain_macro_mem_compact
    (scale : ℝ) (ν : ι → ℤ) {z : ι → ℝ} (hz : z ∈ physicalSceneRootGridDomain scale ν) :
    scale⁻¹ • z ∈ Box.Icc (unitPartition.box 1 ν) := Box.coe_subset_Icc hz

/-- A nonnegative full-Haar readout supported in finitely many original root
boxes is exactly the sum of the corresponding unchanged normalized root laws. -/
theorem sum_lintegral_cavityRoot_grid_eq
    (scale N : ℝ) (cells : Finset (ι → ℤ)) (f : (ι → ℝ) → ℝ≥0∞)
    (hsub : Function.support f ⊆ ⋃ ν ∈ cells, physicalSceneRootGridDomain scale ν) :
    (∑ ν ∈ cells, ∫⁻ z, f z ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N) =
      ∫⁻ z, f z ∂cavityRootMeasure volume univ N := by
  simp only [cavityRootMeasure, lintegral_smul_measure, smul_eq_mul, Measure.restrict_univ]
  rw [← Finset.mul_sum, ← lintegral_biUnion_finset
    (fun _ _ _ _ h ↦ pairwise_disjoint_physicalSceneRootGridDomain scale h)
    (fun ν _ ↦ measurableSet_physicalSceneRootGridDomain scale ν)]
  exact congrArg (fun x ↦ (ENNReal.ofReal N)⁻¹ * x) (setLIntegral_eq_of_support_subset hsub)

end OTSelector.Reconstruction

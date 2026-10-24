import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalTwoEdgeSwap
import OTSelector.MeasureTheory.LocalFiniteMeasureKernel
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Measurable actual two-edge exchanges

The original locally finite plan is its own S-finite measurable kernel.
Evaluating it on the complement of two parameter-dependent singletons proves
joint measurability of the actual deletion and reinsertion operation.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false

/-- Removing two specified original atoms is measurable even though the
restriction set depends on those actual atom coordinates. -/
theorem measurable_originalMeasureDeletePair
    {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] :
    Measurable (fun p : LocalFiniteMeasure X × (X × X) ↦
      (p.1 : Measure X).restrict ({p.2.1, p.2.2} : Set X)ᶜ) := by
  let κ : Kernel (LocalFiniteMeasure X × (X × X)) X :=
    localFiniteMeasureKernel.comap Prod.fst measurable_fst
  apply Measure.measurable_of_measurable_coe
  intro U hU
  let T : Set ((LocalFiniteMeasure X × (X × X)) × X) :=
    {p | p.2 ∈ U ∧ p.2 ≠ p.1.2.1 ∧ p.2 ≠ p.1.2.2}
  have hT : MeasurableSet T :=
    (measurable_snd hU).inter
      ((measurableSet_eq_fun measurable_snd measurable_fst.snd.fst).compl.inter
        (measurableSet_eq_fun measurable_snd measurable_fst.snd.snd).compl)
  have heq : (fun p : LocalFiniteMeasure X × (X × X) ↦
      (p.1 : Measure X).restrict ({p.2.1, p.2.2} : Set X)ᶜ U) =
      fun p ↦ κ p (Prod.mk p ⁻¹' T) := by
    funext p
    rw [Measure.restrict_apply hU]
    congr 1
    ext x
    simp [T, and_assoc]
    tauto
  rw [heq]
  exact κ.measurable_kernel_prodMk_left hT

/-- The full actual deletion and insertion of crossed partners is jointly Borel. -/
theorem measurable_originalTwoEdgeSwapPlan (q : ℕ) :
    Measurable (fun p : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) ×
      (LegalMarkedPhysicalEdge q × LegalMarkedPhysicalEdge q) ↦
      originalTwoEdgeSwapPlan p.1 p.2.1 p.2.2) := by
  apply measurable_localFiniteMeasure_of_measurable_measure
  exact (measurable_originalMeasureDeletePair.add
    (Measure.measurable_dirac.comp (measurable_snd.fst.fst.prodMk measurable_snd.snd.snd))).add
      (Measure.measurable_dirac.comp (measurable_snd.snd.fst.prodMk measurable_snd.fst.snd))

/-- The measurable operation retains the whole same-scene original input. -/
theorem measurable_originalTwoEdgeSwapScene (q : ℕ) :
    Measurable (fun p : LegalMarkedOptimalInputScene q ×
      (LegalMarkedPhysicalEdge q × LegalMarkedPhysicalEdge q) ↦
      originalTwoEdgeSwapScene p.1 p.2.1 p.2.2) := by
  exact (((measurable_originalTwoEdgeSwapPlan q).comp
    (measurable_fst.fst.fst.prodMk measurable_snd)).prodMk measurable_fst.fst.snd).prodMk
      measurable_fst.snd

end OTSelector.Reconstruction

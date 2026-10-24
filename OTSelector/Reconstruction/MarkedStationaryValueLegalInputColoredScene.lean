import OTSelector.Reconstruction.MarkedStationaryValueLegalInputLaplace
import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalSceneCollarTail
import OTSelector.MeasureTheory.LocalFiniteMeasureTightness
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish

/-!
# The same original input point measures with immutable colors

The source and target colors are retained in an explicit finite tag. Both
original finite prefixes use exactly the same physical center and original
Haar root as their legal optimum. No clock separation or selected-point law is
needed to recover either color.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Literal counting measure of one finite original point enumeration. -/
def legalInputBlockMeasure {X : Type*} [MeasurableSpace X] (b : BlockData X) : Measure X :=
  ∑ i : Fin b.1, Measure.dirac (b.2 i)

instance legalInputBlockMeasureIsFinite {X : Type*} [MeasurableSpace X] (b : BlockData X) :
    IsFiniteMeasure (legalInputBlockMeasure b) := by
  unfold legalInputBlockMeasure
  infer_instance

theorem measurable_legalInputBlockMeasure {X : Type*} [MeasurableSpace X] :
    Measurable (legalInputBlockMeasure (X := X)) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS T hT
  change MeasurableSet[⨅ n : ℕ,
    (inferInstance : MeasurableSpace (Fin n → X)).map (Sigma.mk n)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  have hm : Measurable (fun b : Fin n → X ↦
      ∑ i : Fin n, Measure.dirac (b i) S) :=
    Finset.measurable_sum _ (fun i _ ↦ (Measure.measurable_coe hS).comp
      (Measure.measurable_dirac.comp (measurable_pi_apply i)))
  change MeasurableSet ((fun b : Fin n → X ↦ legalInputBlockMeasure ⟨n, b⟩ S) ⁻¹' T)
  simpa only [legalInputBlockMeasure, Measure.finsetSum_apply] using hm hT

/-- Both immutable colors are carried alongside the unchanged physical clock. -/
abbrev LegalColoredInputPoint (q : ℕ) := LegalMarkedPhysicalPoint q × Fin 2

/-- Rooted original input measure, with color zero for every source and color
one for every target. The same root is shared by both original used prefixes. -/
def legalMarkedRootedColoredInputMeasure (q : ℕ) (L : ℝ)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) : Measure (LegalColoredInputPoint q) :=
  legalInputBlockMeasure (mapBlockData (fun x ↦ (x, (0 : Fin 2)))
    (legalInputRootWindowPrefix q (Real.toNNReal L) univ (p.2, p.1.1))) +
  legalInputBlockMeasure (mapBlockData (fun x ↦ (x, (1 : Fin 2)))
    (legalInputRootWindowPrefix q (Real.toNNReal L) univ (p.2, p.1.2)))

instance legalMarkedRootedColoredInputMeasureIsFinite (q : ℕ) (L : ℝ)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) :
    IsFiniteMeasure (legalMarkedRootedColoredInputMeasure q L p) := by
  unfold legalMarkedRootedColoredInputMeasure
  infer_instance

theorem measurable_legalMarkedRootedColoredInputMeasure (q : ℕ) (L : ℝ) :
    Measurable (legalMarkedRootedColoredInputMeasure q L) := by
  have hbase := measurable_legalInputRootWindowPrefix q (Real.toNNReal L) MeasurableSet.univ
  have hs : Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      legalInputBlockMeasure (mapBlockData (fun x ↦ (x, (0 : Fin 2)))
        (legalInputRootWindowPrefix q (Real.toNNReal L) univ (p.2, p.1.1)))) :=
    measurable_legalInputBlockMeasure.comp ((measurable_mapBlockData
      (measurable_id.prodMk measurable_const)).comp
        (hbase.comp (measurable_snd.prodMk measurable_fst.fst)))
  have ht : Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      legalInputBlockMeasure (mapBlockData (fun x ↦ (x, (1 : Fin 2)))
        (legalInputRootWindowPrefix q (Real.toNNReal L) univ (p.2, p.1.2)))) :=
    measurable_legalInputBlockMeasure.comp ((measurable_mapBlockData
      (measurable_id.prodMk measurable_const)).comp
        (hbase.comp (measurable_snd.prodMk measurable_fst.snd)))
  apply Measure.measurable_of_measurable_coe
  intro S hS
  convert ((Measure.measurable_coe hS).comp hs).add ((Measure.measurable_coe hS).comp ht) using 1
  funext p
  exact Measure.add_apply _ _ S

local instance markedStationaryValueLegalInputColoredSceneLocalPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual same-root colored inputs in their vague point-measure carrier. -/
def legalMarkedRootedColoredInputLocal (q : ℕ) (L : ℝ)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) :
    LocalFiniteMeasure (LegalColoredInputPoint q) :=
  ⟨legalMarkedRootedColoredInputMeasure q L p, inferInstance⟩

theorem measurable_legalMarkedRootedColoredInputLocal (q : ℕ) (L : ℝ) :
    Measurable (legalMarkedRootedColoredInputLocal q L) := by
  apply measurable_localFiniteMeasure_of_measurable_measure
  exact measurable_legalMarkedRootedColoredInputMeasure q L

/-- Finite input integration is exactly its original point sum. -/
theorem integral_legalInputBlockMeasure {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (b : BlockData X) (h : X → ℝ) :
    (∫ x, h x ∂legalInputBlockMeasure b) = legalInputBlockTest h b := by
  unfold legalInputBlockMeasure
  rw [integral_finsetSum_measure (fun i _ ↦ integrable_dirac (by simp))]
  simp only [integral_dirac, legalInputBlockTest]

/-- Both original colors can be tested independently in the same rooted
point measure, even when their scalar clock supports overlap or interleave. -/
theorem integral_legalMarkedRootedColoredInputMeasure
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (F : LegalColoredInputPoint q → ℝ)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) :
    (∫ x, F x ∂legalMarkedRootedColoredInputMeasure q L p) =
      legalMarkedRootedSourceInputTest q L (fun x ↦ F (x, 0)) p.1 p.2 +
        legalMarkedRootedTargetInputTest q L (fun x ↦ F (x, 1)) p.1 p.2 := by
  have hfi (b : BlockData (LegalColoredInputPoint q)) : Integrable F (legalInputBlockMeasure b) := by
    unfold legalInputBlockMeasure
    exact integrable_finsetSum_measure.mpr (fun i _ ↦ integrable_dirac (by simp))
  rw [legalMarkedRootedColoredInputMeasure, integral_add_measure (hfi _) (hfi _),
    integral_legalInputBlockMeasure, integral_legalInputBlockMeasure]
  change legalInputBlockTest (fun x ↦ F (x, 0))
      (legalInputRootWindowPrefix q (Real.toNNReal L) univ (p.2, p.1.1)) +
    legalInputBlockTest (fun x ↦ F (x, 1))
      (legalInputRootWindowPrefix q (Real.toNNReal L) univ (p.2, p.1.2)) = _
  rw [legalInputBlockTest_rootWindow_sourceInput q hL univ _ (fun x hx ↦ (hx (mem_univ _)).elim),
    legalInputBlockTest_rootWindow_targetInput q hL univ _ (fun x hx ↦ (hx (mem_univ _)).elim)]

end OTSelector.Reconstruction

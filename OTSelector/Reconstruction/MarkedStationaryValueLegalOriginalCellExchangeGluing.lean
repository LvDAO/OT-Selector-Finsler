import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCycleLocalPatch
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCountingMeasureSum

/-!
# Literal complete-cell gluing of original legal exchanges

The original crossing-edge piece is retained unchanged. Each disjoint
complete-cell piece can undergo its actual two-edge exchange. Their literal
locally finite measure sum retains the original whole source and target
marginals, the integer full matching and strict forward support.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false

/-- A cell's two actual unit atoms already suffice to preserve both complete
marginals; no full matching assertion on an isolated cell is required. -/
theorem originalTwoEdgeSwapPlan_marginals_of_unit_atoms {q : ℕ}
    (μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) {e f : LegalMarkedPhysicalEdge q}
    (hne : e ≠ f) (he : (μ : Measure (LegalMarkedPhysicalEdge q)) {e} = 1)
    (hf : (μ : Measure (LegalMarkedPhysicalEdge q)) {f} = 1) :
    (originalTwoEdgeSwapPlan μ e f : Measure (LegalMarkedPhysicalEdge q)).fst =
      (μ : Measure (LegalMarkedPhysicalEdge q)).fst ∧
    (originalTwoEdgeSwapPlan μ e f : Measure (LegalMarkedPhysicalEdge q)).snd =
      (μ : Measure (LegalMarkedPhysicalEdge q)).snd := by
  have hdec := measure_eq_restrict_compl_add_two_dirac
    (μ : Measure (LegalMarkedPhysicalEdge q)) hne he hf
  constructor
  · change (((μ : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ +
      Measure.dirac (e.1, f.2)) + Measure.dirac (f.1, e.2)).fst = _
    conv_rhs => rw [hdec]
    simp only [Measure.fst_add]
    simp only [Measure.fst, Measure.map_dirac]
  · change (((μ : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ +
      Measure.dirac (e.1, f.2)) + Measure.dirac (f.1, e.2)).snd = _
    conv_rhs => rw [hdec]
    simp only [Measure.snd_add]
    simp only [Measure.snd, Measure.map_dirac]
    abel

/-- An almost-everywhere assertion on the original integer carrier holds at
every occupied edge, with no continuity requirement on the assertion. -/
theorem forall_support_of_ae_of_legalCounting
    {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] (base : X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) {P : X → Prop}
    (hP : ∀ᵐ x ∂(μ : Measure X), P x) : ∀ x ∈ (μ : Measure X).support, P x := by
  intro x hx
  by_contra hbad
  have hzero : (μ : Measure X) {x} = 0 :=
    measure_mono_null (singleton_subset_iff.mpr hbad) (ae_iff.mp hP)
  have hunit := one_le_singleton_of_mem_support_of_legalCounting base μ hμ hx
  rw [hzero] at hunit
  norm_num at hunit

/-- The actual crossing piece plus the literal locally finite exchanged cell pieces. -/
def originalCellGluedPlan {q : ℕ} {ι : Type*}
    (μ₀ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (ν : ι → LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (hν : IsFiniteMeasureOnCompacts
      (Measure.sum (fun i ↦ (ν i : Measure (LegalMarkedPhysicalEdge q))))) :
    LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
  ⟨(μ₀ : Measure (LegalMarkedPhysicalEdge q)) + Measure.sum (fun i ↦ (ν i : Measure (LegalMarkedPhysicalEdge q))), by
    let : IsFiniteMeasureOnCompacts (Measure.sum (fun i ↦ (ν i : Measure (LegalMarkedPhysicalEdge q)))) := hν
    constructor
    intro K hK
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩

/-- Reassembled actual cells retain the same complete original colored input. -/
def originalCellGluedScene {q : ℕ} {ι : Type*} (s : LegalMarkedOptimalInputScene q)
    (μ₀ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (ν : ι → LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (hν : IsFiniteMeasureOnCompacts
      (Measure.sum (fun i ↦ (ν i : Measure (LegalMarkedPhysicalEdge q))))) :
    LegalMarkedOptimalInputScene q := ((originalCellGluedPlan μ₀ ν hν, s.1.2), s.2)

/-- Countably many Borel actual exchanged pieces give a Borel actual global plan. -/
theorem measurable_originalCellGluedPlan {q : ℕ} {ι Ω : Type*}
    [Countable ι] [MeasurableSpace Ω]
    (μ₀ : Ω → LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) (hμ₀ : Measurable μ₀)
    (ν : Ω → ι → LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (hνm : ∀ i, Measurable (fun ω ↦ ν ω i))
    (hν : ∀ ω, IsFiniteMeasureOnCompacts
      (Measure.sum (fun i ↦ (ν ω i : Measure (LegalMarkedPhysicalEdge q))))) :
    Measurable (fun ω ↦ originalCellGluedPlan (μ₀ ω) (ν ω) (hν ω)) := by
  apply measurable_localFiniteMeasure_of_measurable_measure
  apply Measure.measurable_of_measurable_coe
  intro A hA
  change Measurable (fun ω ↦ ((μ₀ ω : Measure (LegalMarkedPhysicalEdge q)) +
    Measure.sum (fun i ↦ (ν ω i : Measure (LegalMarkedPhysicalEdge q)))) A)
  simp only [Measure.add_apply, Measure.sum_apply _ hA]
  exact (((Measure.measurable_coe hA).comp
    (measurable_localFiniteMeasure_coe.comp hμ₀)).add
      (Measurable.tsum fun i ↦ (Measure.measurable_coe hA).comp
        (measurable_localFiniteMeasure_coe.comp (hνm i))))

/-- Same-input original integer pieces and exact local marginal conservation
assemble an actual full one-to-one matching of every unchanged original atom. -/
theorem IsFullOriginalInputMatching.cellGlue {q : ℕ} {ι : Type*}
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (μ₀ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (μ ν : ι → LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (hν : IsFiniteMeasureOnCompacts
      (Measure.sum (fun i ↦ (ν i : Measure (LegalMarkedPhysicalEdge q)))))
    (hdec : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) =
      (μ₀ : Measure (LegalMarkedPhysicalEdge q)) + Measure.sum (fun i ↦ (μ i : Measure (LegalMarkedPhysicalEdge q))))
    (hc₀ : IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) μ₀)
    (hcν : ∀ i, IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) (ν i))
    (hmarg : ∀ i, (ν i : Measure (LegalMarkedPhysicalEdge q)).fst = (μ i : Measure (LegalMarkedPhysicalEdge q)).fst ∧
      (ν i : Measure (LegalMarkedPhysicalEdge q)).snd = (μ i : Measure (LegalMarkedPhysicalEdge q)).snd) :
    IsFullOriginalInputMatching q (originalCellGluedScene s μ₀ ν hν) := by
  let : IsFiniteMeasureOnCompacts
      (Measure.sum (fun i ↦ (ν i : Measure (LegalMarkedPhysicalEdge q)))) := hν
  have hcSum := isLegalCountingMeasure_sum (0 : LegalMarkedPhysicalEdge q) ν hcν
  have hcAll := isLegalCountingMeasure_add (0 : LegalMarkedPhysicalEdge q) μ₀
    ⟨Measure.sum (fun i ↦ (ν i : Measure (LegalMarkedPhysicalEdge q))), hν⟩ hc₀ hcSum
  apply isFullOriginalInputMatching_of_counting_simple_marginals
  · exact hcAll
  · exact hs.simple_inputs
  · constructor
    · change ((μ₀ : Measure (LegalMarkedPhysicalEdge q)) +
        Measure.sum (fun i ↦ (ν i : Measure (LegalMarkedPhysicalEdge q)))).fst =
        legalInputColorMeasure q s.2 0
      rw [← hs.source_marginal]
      conv_rhs => rw [hdec]
      simp only [Measure.fst_add, Measure.fst_sum]
      exact congrArg (fun a ↦ (μ₀ : Measure (LegalMarkedPhysicalEdge q)).fst + a)
        (congrArg Measure.sum (funext fun i ↦ (hmarg i).1))
    · change ((μ₀ : Measure (LegalMarkedPhysicalEdge q)) +
        Measure.sum (fun i ↦ (ν i : Measure (LegalMarkedPhysicalEdge q)))).snd =
        legalInputColorMeasure q s.2 1
      rw [← hs.target_marginal]
      conv_rhs => rw [hdec]
      simp only [Measure.snd_add, Measure.snd_sum]
      exact congrArg (fun a ↦ (μ₀ : Measure (LegalMarkedPhysicalEdge q)).snd + a)
        (congrArg Measure.sum (funext fun i ↦ (hmarg i).2))

/-- Strict forward legality survives the complete countable cell assembly
because every resulting support edge is an actual occupied integer atom. -/
theorem forward_originalCellGluedScene {q : ℕ} {ι : Type*} [Countable ι]
    (s : LegalMarkedOptimalInputScene q)
    (μ₀ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (ν : ι → LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (hν : IsFiniteMeasureOnCompacts
      (Measure.sum (fun i ↦ (ν i : Measure (LegalMarkedPhysicalEdge q)))))
    (hc : IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) (originalCellGluedPlan μ₀ ν hν))
    (hf₀ : ∀ e ∈ (μ₀ : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2)
    (hfν : ∀ i, ∀ e ∈ (ν i : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2) :
    ∀ e ∈ ((originalCellGluedScene s μ₀ ν hν).1.1 :
      Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
  change ∀ e ∈ (originalCellGluedPlan μ₀ ν hν :
    Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2
  apply forall_support_of_ae_of_legalCounting _ _ hc (P := fun e ↦ e.1.2 < e.2.2)
  change ∀ᵐ e ∂((μ₀ : Measure (LegalMarkedPhysicalEdge q)) +
    Measure.sum (fun i ↦ (ν i : Measure (LegalMarkedPhysicalEdge q)))), e.1.2 < e.2.2
  rw [ae_add_measure_iff, Measure.ae_sum_iff]
  constructor
  · filter_upwards [(μ₀ : Measure (LegalMarkedPhysicalEdge q)).support_mem_ae] with e he
    exact hf₀ e he
  · intro i
    filter_upwards [(ν i : Measure (LegalMarkedPhysicalEdge q)).support_mem_ae] with e he
    exact hfν i e he

end OTSelector.Reconstruction

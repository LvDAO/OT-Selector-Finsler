import OTSelector.Reconstruction.MarkedStationaryValueLegalSpatialTypesFinite
import OTSelector.Reconstruction.MarkedStationaryValueLegalSpatialTypes
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonDefect

/-!
# Actual original spatial legal source-defect expectation

Point types combine spatial cells and population labels. The deterministic
same-type original comparator and the exact original joint Poisson histogram
law yield the expectation of the literal legal hierarchy defects.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Original common point-type laws control the actual sum of legal child
deficiencies, without equal spatial cell masses or realized type balance. -/
theorem integral_spatialLegalMarkedSourceDefectSum_le_of_pointTypes (q : ℕ)
    {β : Type*} [Fintype β] [DecidableEq β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {cell : (Fin q → ℝ) → β} {source : A → ℝ} {target : B → ℝ}
    (hc : Measurable cell) (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (βlaw : Measure B) [IsProbabilityMeasure βlaw]
    {K : ℕ} [NeZero K]
    {tagA : ((Fin q → ℝ) × A) → Fin K} {tagB : ((Fin q → ℝ) × B) → Fin K}
    (hA : Measurable tagA) (hB : Measurable tagB)
    (L : Measure (Fin K)) [IsProbabilityMeasure L]
    (hLA : ((cubeMeasure (Fin q) 1).prod α).map tagA = L)
    (hLB : ((cubeMeasure (Fin q) 1).prod βlaw).map tagB = L) (r : ℝ≥0)
    (hlegal : ∀ᵐ ω ∂twoMarkedCloudLaw q A B α βlaw r,
      ∀ (i : Fin (mSourceCount ω)) (j : Fin (mTargetCount ω)),
        tagA (ω.1.2 i) = tagB (ω.2.2 j) →
          source (mSourceMark ω i) < target (mTargetMark ω j) ∧
            cell (mSourcePoint ω i) = cell (mTargetPoint ω j)) :
    Integrable (spatialLegalMarkedSourceDefectSum q cell source target)
      (twoMarkedCloudLaw q A B α βlaw r) ∧
      (∫ ω, spatialLegalMarkedSourceDefectSum q cell source target ω
        ∂twoMarkedCloudLaw q A B α βlaw r) ≤ Real.sqrt (2 * (r : ℝ) * K) := by
  obtain ⟨hdiscI, hdiscB⟩ := pointType_discrepancy_integrable_bound q α βlaw
    hA hB L hLA hLB r
  have hdefI := integrable_spatialLegalMarkedSourceDefectSum q hc hs ht α βlaw r
  have himbalance : Integrable (fun ω : TwoMarkedCloudSpace q A B ↦
      (mSourceCount ω : ℝ) - ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ))
      (twoMarkedCloudLaw q A B α βlaw r) :=
    (integrable_mSourceCount q α βlaw r).sub (integrable_mMinCount q α βlaw r)
  have hboundI : Integrable (fun ω : TwoMarkedCloudSpace q A B ↦
      (1 / 2 : ℝ) * pointTypeDiscrepancy tagA tagB ω +
        ((mSourceCount ω : ℝ) - ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)))
      (twoMarkedCloudLaw q A B α βlaw r) := (hdiscI.const_mul _).add himbalance
  have hpt : ∀ᵐ ω ∂twoMarkedCloudLaw q A B α βlaw r,
      spatialLegalMarkedSourceDefectSum q cell source target ω ≤
        (1 / 2 : ℝ) * pointTypeDiscrepancy tagA tagB ω +
          ((mSourceCount ω : ℝ) - ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)) := by
    filter_upwards [hlegal] with ω hω
    have h := sum_spatialLegalSourceDefects_le_joint_type_discrepancy
      (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) source target ω)
      (fun i ↦ cell (mSourcePoint ω i)) (fun j ↦ cell (mTargetPoint ω j))
      (fun i ↦ tagA (ω.1.2 i)) (fun j ↦ tagB (ω.2.2 j))
      (by
        intro i j hij
        have h := hω i j hij
        exact ⟨by simpa only [legalMarkedGraph, Finset.mem_filter, Finset.mem_univ,
          true_and] using h.1, h.2⟩)
    rw [spatialLegalMarkedSourceDefectSum_eq_nat]
    exact h
  have h := integral_mono_ae hdefI hboundI hpt
  rw [integral_add (hdiscI.const_mul _) himbalance, integral_const_mul] at h
  have himbalanceB := integral_sourceCount_sub_min_le q α βlaw r
  have hscale : Real.sqrt (2 * (r : ℝ)) ≤ Real.sqrt (2 * (r : ℝ) * K) :=
    Real.sqrt_le_sqrt (le_mul_of_one_le_right (by positivity)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)))
  exact ⟨hdefI, by linarith⟩

/-- The common original mark types are combined with the actual spatial cell.
Their exact product law discharges every spatial histogram and legality input. -/
theorem integral_spatialLegalMarkedSourceDefectSum_le_of_typeRectangles (q : ℕ)
    {β : Type*} [Fintype β] [DecidableEq β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {cell : (Fin q → ℝ) → β} {source : A → ℝ} {target : B → ℝ}
    (hc : Measurable cell) (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (βlaw : Measure B) [IsProbabilityMeasure βlaw]
    {K : ℕ} [NeZero K] {tagA : A → Fin K} {tagB : B → Fin K}
    (hA : Measurable tagA) (hB : Measurable tagB)
    (L : Measure (Fin K)) [IsProbabilityMeasure L]
    (hLA : α.map tagA = L) (hLB : βlaw.map tagB = L) (r : ℝ≥0)
    (hlegal : ∀ᵐ p ∂α.prod βlaw,
      tagA p.1 = tagB p.2 → source p.1 < target p.2) :
    Integrable (spatialLegalMarkedSourceDefectSum q cell source target)
      (twoMarkedCloudLaw q A B α βlaw r) ∧
      (∫ ω, spatialLegalMarkedSourceDefectSum q cell source target ω
        ∂twoMarkedCloudLaw q A B α βlaw r) ≤
          Real.sqrt (2 * (r : ℝ) * (Fintype.card β * K)) := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  let N := Fintype.card (β × Fin K)
  let e : β × Fin K ≃ Fin N := Fintype.equivFin _
  have he : Measurable e := measurable_of_countable _
  let cLaw := (cubeMeasure (Fin q) 1).map cell
  have : IsProbabilityMeasure cLaw := Measure.isProbabilityMeasure_map hc.aemeasurable
  let LJ := (cLaw.prod L).map e
  have : IsProbabilityMeasure LJ := Measure.isProbabilityMeasure_map he.aemeasurable
  let tagPA : ((Fin q → ℝ) × A) → Fin N := fun p ↦ e (cell p.1, tagA p.2)
  let tagPB : ((Fin q → ℝ) × B) → Fin N := fun p ↦ e (cell p.1, tagB p.2)
  have hPA : Measurable tagPA := he.comp ((hc.comp measurable_fst).prodMk (hA.comp measurable_snd))
  have hPB : Measurable tagPB := he.comp ((hc.comp measurable_fst).prodMk (hB.comp measurable_snd))
  have hpairA : Measurable (fun p : (Fin q → ℝ) × A ↦ (cell p.1, tagA p.2)) :=
    (hc.comp measurable_fst).prodMk (hA.comp measurable_snd)
  have hpairB : Measurable (fun p : (Fin q → ℝ) × B ↦ (cell p.1, tagB p.2)) :=
    (hc.comp measurable_fst).prodMk (hB.comp measurable_snd)
  have hPLA : ((cubeMeasure (Fin q) 1).prod α).map tagPA = LJ := by
    change ((cubeMeasure (Fin q) 1).prod α).map
      (e ∘ (fun p ↦ (cell p.1, tagA p.2))) = _
    rw [← Measure.map_map he hpairA,
      map_point_jointSpatialType q α hc hA, hLA]
  have hPLB : ((cubeMeasure (Fin q) 1).prod βlaw).map tagPB = LJ := by
    change ((cubeMeasure (Fin q) 1).prod βlaw).map
      (e ∘ (fun p ↦ (cell p.1, tagB p.2))) = _
    rw [← Measure.map_map he hpairB,
      map_point_jointSpatialType q βlaw hc hB, hLB]
  have hNpos : 0 < N := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(cell (fun _ ↦ 0), ⟨0, Nat.pos_of_ne_zero (NeZero.ne K)⟩)⟩
  let : NeZero N := ⟨hNpos.ne'⟩
  have hcloud := ae_markedCloud_forward_of_typeRectangles q α βlaw source target
    tagA tagB r hlegal
  have hlegalJ : ∀ᵐ ω ∂twoMarkedCloudLaw q A B α βlaw r,
      ∀ (i : Fin (mSourceCount ω)) (j : Fin (mTargetCount ω)),
        tagPA (ω.1.2 i) = tagPB (ω.2.2 j) →
          source (mSourceMark ω i) < target (mTargetMark ω j) ∧
            cell (mSourcePoint ω i) = cell (mTargetPoint ω j) := by
    filter_upwards [hcloud] with ω hω
    intro i j hij
    have hp := e.injective hij
    exact ⟨hω i j (congrArg Prod.snd hp), congrArg Prod.fst hp⟩
  have h := integral_spatialLegalMarkedSourceDefectSum_le_of_pointTypes q hc hs ht α βlaw
    hPA hPB LJ hPLA hPLB r hlegalJ
  simpa only [N, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using h

end OTSelector.Reconstruction

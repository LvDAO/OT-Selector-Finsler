import OTSelector.Reconstruction.OriginalReserveClassCapacityLimit
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlockExtremes

/-! All actual positive-block extreme reserve capacities hold outside a quadratically negligible event. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Finite unions preserve the actual quadratically negligible probability
bounds, without independence of any of the constituent events. -/
theorem tendsto_quadratic_finite_union_measureReal_zero {Ω I : Type*}
    [MeasurableSpace Ω] [Fintype I] (P : ℝ → Measure Ω) (bad : I → ℝ → Set Ω)
    (h : ∀ i, Tendsto (fun R ↦ R^2 * (P R).real (bad i R)) atTop (𝓝 0)) :
    Tendsto (fun R ↦ R^2 * (P R).real {p | ∃ i, p ∈ bad i R}) atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum Finset.univ (fun i _ ↦ h i)
  simp only [Finset.sum_const_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall fun R ↦ mul_nonneg (sq_nonneg R) measureReal_nonneg)
    (Eventually.of_forall fun R ↦ ?_) hsum
  have hb : (P R).real {p | ∃ i, p ∈ bad i R} ≤ ∑ i, (P R).real (bad i R) := by
    convert measureReal_iUnion_fintype_le (μ := P R) (fun i ↦ bad i R) using 1
    congr 1
    ext p
    simp
  exact (mul_le_mul_of_nonneg_left hb (sq_nonneg R)).trans_eq (Finset.mul_sum _ _ _)

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}

/-- Every positive actual Hall block supplies its own positive first-source
and last-target class internally. Their real theta-reserve half-mean capacities
fail jointly only with quadratically negligible probability on the same joins. -/
theorem tendsto_positiveBlockExtreme_capacity_failure (hq : 4 < q)
    (X : ∀ R : ℝ, 0 < R → OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
    (G : OriginalStageClockGrid)
    (hmono : ∀ i, α (G.sourceCell i) = 0 ∨ β (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus α β k) :
    Tendsto (fun R : ℝ ↦ if hR : 0 < R then
      R^2 * ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        {p | ∃ block : G.ClockSlabBlock α β, block ∈ G.positiveSlabBlocks α β ∧
          ((originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) (G.sourceCell (G.firstBlockClass block)) : ℝ) < (((Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (α (G.sourceCell (G.firstBlockClass block))).toNNReal : ℝ≥0) : ℝ) / 2 ∨
            (originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) (G.targetCell (G.lastBlockClass block)) : ℝ) < (((Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (β (G.targetCell (G.lastBlockClass block))).toNNReal : ℝ≥0) : ℝ) / 2)}
      else 0) atTop (𝓝 0) := by
  let B := ↥(G.positiveSlabBlocks α β)
  let P : ℝ → Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) :=
    fun R ↦ if hR : 0 < R then ((X R hR).fullLaw : Measure _) else 0
  let bad : B ⊕ B → ℝ → Set (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) :=
    fun i R ↦ i.elim
      (fun item ↦ let block := item.val; {p | (originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) (G.sourceCell (G.firstBlockClass block)) : ℝ) < (((Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (α (G.sourceCell (G.firstBlockClass block))).toNNReal : ℝ≥0) : ℝ) / 2})
      (fun item ↦ let block := item.val; {p | (originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) (G.targetCell (G.lastBlockClass block)) : ℝ) < (((Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (β (G.targetCell (G.lastBlockClass block))).toNNReal : ℝ≥0) : ℝ) / 2})
  have hi (i : B ⊕ B) : Tendsto (fun R ↦ R^2 * (P R).real (bad i R)) atTop (𝓝 0) := by
    cases i with
    | inl item =>
      have hmass := (G.positiveSlabBlock_extreme_class_masses hmono hH item.val item.property).1
      have hh := tendsto_sourceReserveBlockCount_lower_probability hq X
        (C := G.sourceCell (G.firstBlockClass item.val)) measurableSet_Ico hmass
      convert hh using 1
      funext R
      by_cases hR : 0 < R
      · simp only [P, bad, Sum.elim_inl, dite_eq_left hR]
      · simp [P, bad, hR]
    | inr item =>
      have hmass := (G.positiveSlabBlock_extreme_class_masses hmono hH item.val item.property).2
      have hh := tendsto_targetReserveBlockCount_lower_probability hq X
        (C := G.targetCell (G.lastBlockClass item.val)) measurableSet_Ioc hmass
      convert hh using 1
      funext R
      by_cases hR : 0 < R
      · simp only [P, bad, Sum.elim_inr, dite_eq_left hR]
      · simp [P, bad, hR]
  have hu := tendsto_quadratic_finite_union_measureReal_zero P bad hi
  convert hu using 1
  funext R
  by_cases hR : 0 < R
  · simp only [P, dite_eq_left hR]
    apply congrArg (fun A : Set (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) ↦
      R^2 * ((X R hR).fullLaw : Measure _).real A)
    ext p
    constructor
    · rintro ⟨block, hb, hs | ht⟩
      · exact ⟨Sum.inl ⟨block, hb⟩, hs⟩
      · exact ⟨Sum.inr ⟨block, hb⟩, ht⟩
    · rintro ⟨i, hi⟩
      cases i with
      | inl item => exact ⟨item.val, item.property, Or.inl hi⟩
      | inr item => exact ⟨item.val, item.property, Or.inr hi⟩
  · simp [P, hR]

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction

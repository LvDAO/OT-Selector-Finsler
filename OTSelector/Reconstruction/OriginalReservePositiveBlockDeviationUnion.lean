import OTSelector.Reconstruction.OriginalReservePositiveBlockCapacityUnion
import OTSelector.Reconstruction.OriginalReserveFullUnitInputBlockDeviationLimit

/-! All actual positive-block imbalances fit their genuine reserve class slack outside a negligible event. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}

/-- The real positive-block excess is below a quarter of each actual extreme
class mean, jointly outside a quadratically negligible event. Strict law slack
and positive extreme masses are produced by the same actual clock blocks. -/
theorem tendsto_positiveBlock_unitDiscrepancy_failure (hq : 4 < q)
    (X : ∀ R : ℝ, 0 < R → OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
    (G : OriginalStageClockGrid)
    (hmono : ∀ i, α (G.sourceCell i) = 0 ∨ β (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus α β k) :
    Tendsto (fun R : ℝ ↦ if hR : 0 < R then
      let K := originalCenteredPhysicalCubeRegion b (2 * R)
      R^2 * ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        {p | ∃ block : G.ClockSlabBlock α β, block ∈ G.positiveSlabBlocks α β ∧
          (θ * min (α.real (G.sourceCell (G.firstBlockClass block)))
            (β.real (G.targetCell (G.lastBlockClass block))) / 4) * volume.real K <
          |(originalMainPhysicalBlockCount K (G.sourceBlockCell α β block) 0
              (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
            (originalMainPhysicalBlockCount K (G.targetBlockCell α β block) 1
              (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)|}
      else 0) atTop (𝓝 0) := by
  let B := ↥(G.positiveSlabBlocks α β)
  let P : ℝ → Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) :=
    fun R ↦ if hR : 0 < R then ((X R hR).fullLaw : Measure _) else 0
  let bad : B → ℝ → Set (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) :=
    fun item R ↦ let K := originalCenteredPhysicalCubeRegion b (2 * R)
      {p | (θ * min (α.real (G.sourceCell (G.firstBlockClass item.val)))
          (β.real (G.targetCell (G.lastBlockClass item.val))) / 4) * volume.real K <
        |(originalMainPhysicalBlockCount K (G.sourceBlockCell α β item.val) 0
            (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
          (originalMainPhysicalBlockCount K (G.targetBlockCell α β item.val) 1
            (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)|}
  have hi (item : B) : Tendsto (fun R ↦ R^2 * (P R).real (bad item R)) atTop (𝓝 0) := by
    have hm := G.positiveSlabBlock_extreme_class_masses hmono hH item.val item.property
    have hr : 0 < θ * min (α.real (G.sourceCell (G.firstBlockClass item.val)))
        (β.real (G.targetCell (G.lastBlockClass item.val))) / 4 :=
      div_pos (mul_pos hθ (lt_min hm.1 hm.2)) (by norm_num)
    have hbal := (ENNReal.toReal_eq_toReal_iff' (measure_ne_top α _) (measure_ne_top β _)).mp
      (G.block_mass_balance item.val)
    have hh := tendsto_unitBlock_discrepancy_probability hq X
      (G.blockCells_measurable item.val).1 (G.blockCells_measurable item.val).2 hbal hr
    convert hh using 1
    funext R
    by_cases hR : 0 < R
    · simp only [P, bad, dite_eq_left hR]
    · simp [P, hR]
  have hu := tendsto_quadratic_finite_union_measureReal_zero P bad hi
  convert hu using 1
  funext R
  by_cases hR : 0 < R
  · simp only [P, dite_eq_left hR]
    apply congrArg (fun A : Set (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) ↦
      R^2 * ((X R hR).fullLaw : Measure _).real A)
    ext p
    constructor
    · rintro ⟨block, hb, hp⟩
      exact ⟨⟨block, hb⟩, hp⟩
    · rintro ⟨item, hp⟩
      exact ⟨item.val, item.property, hp⟩
  · simp [P, hR]

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction

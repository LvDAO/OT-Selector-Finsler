import OTSelector.Reconstruction.OriginalReserveFullUnitInputBlockExcess
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlockExtremes

/-! Actual count good events internally produce deletion capacity and protected reserve slack. -/
open Set Function MeasureTheory ProbabilityTheory
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
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- Real half-mean extreme-class counts and a quarter-mean actual block
imbalance produce both exact deletion capacities and a positive retained
reserve slack. All quantities read the same original scene and reserve indices. -/
theorem ae_blockCapacity_of_goodCounts (G : OriginalStageClockGrid) (block : G.ClockSlabBlock α β) :
    let K := originalCenteredPhysicalCubeRegion b (2 * R)
    let Cs := G.sourceCell (G.firstBlockClass block)
    let Ct := G.targetCell (G.lastBlockClass block)
    let r := θ * min (α.real Cs) (β.real Ct) / 4
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      let Ns := originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) Cs
      let Nt := originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) Ct
      let es := originalReserveBlockExcess K 0 1 (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
        (originalReserveExcessInputAux (originalReserveUnitSourceSamplerView q θ hθ1 p))
      let et := originalReserveBlockExcess K 1 0 (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
        (originalReserveExcessInputAux (originalReserveUnitTargetSamplerView q θ hθ1 p))
      θ * volume.real K * α.real Cs / 2 ≤ (Ns : ℝ) →
      θ * volume.real K * β.real Ct / 2 ≤ (Nt : ℝ) →
      |(originalMainPhysicalBlockCount K (G.sourceBlockCell α β block) 0
          (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ) -
        (originalMainPhysicalBlockCount K (G.targetBlockCell α β block) 1
          (originalReserveUnitInputReadout q θ hθ hθ1 p.1) : ℝ)| ≤ r * volume.real K →
      es ≤ Ns ∧ et ≤ Nt ∧ r * volume.real K ≤ ((Ns - es : ℕ) : ℝ) ∧
        r * volume.real K ≤ ((Nt - et : ℕ) : ℝ) := by
  dsimp only
  filter_upwards [X.ae_blockRequestedExcess_eq_unit (G.blockCells_measurable block).1
    (G.blockCells_measurable block).2] with p hp
  intro hs ht hd
  let V := volume.real (originalCenteredPhysicalCubeRegion b (2 * R))
  let ws := α.real (G.sourceCell (G.firstBlockClass block))
  let wt := β.real (G.targetCell (G.lastBlockClass block))
  let d := (θ * min ws wt / 4) * V
  change θ * V * ws / 2 ≤ _ at hs
  change θ * V * wt / 2 ≤ _ at ht
  change _ ≤ d at hd
  have hd0 : 0 ≤ d := mul_nonneg (div_nonneg (mul_nonneg hθ.le
    (le_min measureReal_nonneg measureReal_nonneg)) (by norm_num)) measureReal_nonneg
  have hms : θ * V * min ws wt ≤ θ * V * ws :=
    mul_le_mul_of_nonneg_left (min_le_left ws wt) (mul_nonneg hθ.le measureReal_nonneg)
  have hmt : θ * V * min ws wt ≤ θ * V * wt :=
    mul_le_mul_of_nonneg_left (min_le_right ws wt) (mul_nonneg hθ.le measureReal_nonneg)
  have hs2 : 2 * d ≤ θ * V * ws / 2 := by dsimp only [d]; nlinarith [hms]
  have ht2 : 2 * d ≤ θ * V * wt / 2 := by dsimp only [d]; nlinarith [hmt]
  have hes : (originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1
      (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
      (originalReserveExcessInputAux (originalReserveUnitSourceSamplerView q θ hθ1 p)) : ℝ) ≤ d := by
    have he := Nat.cast_nonneg (α := ℝ) (originalReserveBlockExcess
      (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0 (G.targetBlockCell α β block)
      (G.sourceBlockCell α β block) (originalReserveExcessInputAux (originalReserveUnitTargetSamplerView q θ hθ1 p)))
    linarith only [hp, hd, he]
  have het : (originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0
      (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
      (originalReserveExcessInputAux (originalReserveUnitTargetSamplerView q θ hθ1 p)) : ℝ) ≤ d := by
    have he := Nat.cast_nonneg (α := ℝ) (originalReserveBlockExcess
      (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1 (G.sourceBlockCell α β block)
      (G.targetBlockCell α β block) (originalReserveExcessInputAux (originalReserveUnitSourceSamplerView q θ hθ1 p)))
    linarith only [hp, hd, he]
  have hsc : originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1
      (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
      (originalReserveExcessInputAux (originalReserveUnitSourceSamplerView q θ hθ1 p)) ≤
      originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2)
        (G.sourceCell (G.firstBlockClass block)) := by
    apply (Nat.cast_le (α := ℝ)).mp
    linarith only [hes, hs2, hs, hd0]
  have htc : originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0
      (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
      (originalReserveExcessInputAux (originalReserveUnitTargetSamplerView q θ hθ1 p)) ≤
      originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2)
        (G.targetCell (G.lastBlockClass block)) := by
    apply (Nat.cast_le (α := ℝ)).mp
    linarith only [het, ht2, ht, hd0]
  refine ⟨hsc, htc, ?_, ?_⟩
  · rw [Nat.cast_sub hsc]
    change d ≤ _
    linarith only [hes, hs2, hs]
  · rw [Nat.cast_sub htc]
    change d ≤ _
    linarith only [het, ht2, ht]

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction

import OTSelector.Reconstruction.FinslerOriginalBlockPartitionExistence

/-!
# Equal-mass fibre partitions, and the mass half of |CellMassPartition|

## Delivered

|EqualMassPartition mu iota w|: a measurable map |cell : M -> iota| whose fibre
masses are the prescribed weights |w| (|mu (cell ⁻¹' {i}) = ofReal (w i)|).

|cellMassPartition_of_equalMass|: given such partitions for the source and target
physical probabilities with |w| the block weights |((blockW q (2^k+1) (by positivity) c :
unitInterval) : R)|, this produces the mass half of |CellMassPartition| -- the
|cellS cellT hcellS hcellT hmassS hmassT| fields -- with the block-weight mass
laws proved by rewriting the fibre masses.

This isolates the equal-mass partition existence from the coordinate/cube-law side;
combined with |cellCoordinateIsomorphisms_of_blockLaws| it yields
|PhysicalBlockTransport| via |physicalBlockTransport_of_blockLaws|.

## Existence of |EqualMassPartition| for atomless measures (exact residual)

For an atomless probability measure on |M| and prescribed weights summing to |1|
(e.g. |1 / N| with |N = (2^k + 1)^q|), the standard construction is a quantile map
obtained from a uniform-valued measurable coordinate (standard-Borel isomorphism /
cumulative distribution).  Mathlib supplies the atomless API and the standard Borel
space API, but no theorem producing a measurable map with a prescribed finite
uniform law from atomlessness; hence |EqualMassPartition| for atomless |mu| and
|w = 1 / N| is the exact typed residual:

  |AtomicFreeEqualMassInput (mu : Measure M) (iota : Type*) (w : iota -> R) : Prop :=
    0 < (sum i, w i) -> IsProbabilityMeasure mu -> atomless mu ->
      exists cell : M -> iota, Measurable cell /        forall i, mu (cell ⁻¹' {i}) = ofReal (w i)|

The paper's atomless clock inputs (|source_clock_atomless|, |target_clock_atomless|
of |FinslerPaperGeometricHypotheses|) supply the atomlessness hypothesis of that
statement once the measurable-isomorphism step is added.

No 'sorry', 'admit' or added axiom occurs.
-/

open Set Function Filter MeasureTheory
open OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ENNReal NNReal

noncomputable section

namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **A measurable fibre partition with prescribed fibre masses.** -/
structure EqualMassPartition [MeasurableSpace M] (μ : Measure M)
    (ι : Type*) [MeasurableSpace ι] (w : ι → ℝ) where
  cell : M → ι
  hcell : Measurable cell
  hmass : ∀ i, μ (cell ⁻¹' {i}) = ENNReal.ofReal (w i)

/-- **The mass half of |CellMassPartition| from equal-mass fibre partitions, with
the block-weight weight identification |hw|.**  The index type is the block index
|Fin q -> Fin (2^k+1)|, whose cardinality is |(2^k+1)^q|, so the equal-mass weights
are |1 |/|(2^k+1)^q|. -/
def cellMassPartition_of_equalMass [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (w : (Fin q → Fin (2 ^ k + 1)) → ℝ)
    (hw : ∀ c, w c = ((blockW q (2 ^ k + 1) (by positivity) c : unitInterval) : ℝ))
    (Dμ : EqualMassPartition (physicalSourceProbability ωM ρ₀ : Measure M)
      (Fin q → Fin (2 ^ k + 1)) w)
    (Dν : EqualMassPartition (physicalTargetProbability ωM ρ₁ : Measure M)
      (Fin q → Fin (2 ^ k + 1)) w) :
    CellMassPartition (M := M) q k ωM ρ₀ ρ₁ where
  cellS := Dμ.cell
  hcellS := Dμ.hcell
  cellT := Dν.cell
  hcellT := Dν.hcell
  hmassS := fun c => by rw [Dμ.hmass c, hw c]
  hmassT := fun c => by rw [Dν.hmass c, hw c]

end OTSelector.Reconstruction

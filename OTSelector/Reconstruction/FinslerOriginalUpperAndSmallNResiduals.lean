import Mathlib.Logic.Basic

/-!
# Upper-lane and small-n residual bundle (V8 → V9)

Audit of the five upper/small-n residual binders of
`FinslerOriginalPaperTheoremFinalV8` (transcribed exactly from its binder block, lines
357-392/700-735/985-1020):

* `hLB : UpperPoolLowerBound qU mU pc (consolidatedStationaryDatum ...)`
* `hcell : ∀ (n : ℕ) (c : Fin qU → Fin mU),
    (frozenMarkedRadius (blockW qU mU hmU) n c) ^ (2 / (qU : ℝ)) ≤ 1`
* `hsmall : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < 1) (n : ℕ),
    n < mU ^ qU - 1 → ∀ (c) (ξ) (i j), cellS ... = c → cellT ... = c → |kinetic − markedKineticKernel| ≤ 2 * ε n * markedKineticKernel`
* `hpcIntr : ∀ (f) (t) (hpert), PopDataIntrinsic F (paperCalibratedPotential ...) qU mU hmU ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t`
* `hRB : UpperPoolReverseBound qU mU pc (consolidatedStationaryDatum ...)`

The paper proves these as side statements; the module packages them as ONE bundle
with the V8 names so V9 can take a single hypothesis.  No discharge is attempted
here: each of the five remains an exact typed residual.
-/

noncomputable section
namespace OTSelector.Reconstruction

/-- The five upper/small-n residuals of the V8 paper theorem, bundled for V9 in the
V8 order: `hLB`, `hcell`, `hsmall`, `hpcIntr`, `hRB`. -/
structure UpperSmallNResiduals (hLB hcell hsmall hpcIntr hRB : Prop) : Prop where
  /-- lower bound of the upper pool. -/
  lowerBound : hLB
  /-- frozen-radius cell bound `radius ^ (2 / qU) ≤ 1`. -/
  cellBound : hcell
  /-- small-n kinetic deviation: `|kinetic − markedKineticKernel| ≤ 2 εₙ · markedKineticKernel`. -/
  smallN : hsmall
  /-- intrinsic pool data. -/
  poolData : hpcIntr
  /-- reverse bound of the upper pool. -/
  reverseBound : hRB

/-- Build the bundle from the five V8 hypotheses (constructor is definitionally the
identity, so V9 can pass `⟨hLB, hcell, hsmall, hpcIntr, hRB⟩`). -/
theorem upperSmallNResiduals (hLB hcell hsmall hpcIntr hRB : Prop)
    (h1 : hLB) (h2 : hcell) (h3 : hsmall) (h4 : hpcIntr) (h5 : hRB) :
    UpperSmallNResiduals hLB hcell hsmall hpcIntr hRB :=
  ⟨h1, h2, h3, h4, h5⟩

/-- V8-shaped extraction: the bundle yields the five hypotheses in V8 order. -/
theorem UpperSmallNResiduals.out {hLB hcell hsmall hpcIntr hRB : Prop}
    (b : UpperSmallNResiduals hLB hcell hsmall hpcIntr hRB) :
    hLB ∧ hcell ∧ hsmall ∧ hpcIntr ∧ hRB :=
  ⟨b.lowerBound, b.cellBound, b.smallN, b.poolData, b.reverseBound⟩

/-- V9 takes the bundle and recovers `hLB` and `hRB` for
`actualUpperReadout_of_lowerBound_and_reverseBound`. -/
theorem UpperSmallNResiduals.lowerBound_and_reverseBound {hLB hcell hsmall hpcIntr hRB : Prop}
    (b : UpperSmallNResiduals hLB hcell hsmall hpcIntr hRB) : hLB ∧ hRB :=
  ⟨b.lowerBound, b.reverseBound⟩

end OTSelector.Reconstruction

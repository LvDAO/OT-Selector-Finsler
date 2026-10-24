import OTSelector.Reconstruction.FinslerOriginalSeedReadoutC1Probe

/-!
# Seed readout regularity: the linear-probe case

This module adds the LINEAR-probe variant of the mark-lane transfer.  When the
actual probe is a linear functional of the shifted seed readout, i.e.
`g e = (f e + c) ⬝ᵥ b + d`, its C1 regularity (recorded as the named hypothesis
`hgC1`) gives the bounded-derivative interface and hence the mark-Lipschitz
constants, uniformly with the quadratic kinetic readout.

Status of the remaining inputs: (1) C1 of the concrete readout along the chart
parameter is still an input `hf`; (2) the linear probe is handled here (C1 given as
the named hypothesis `hgC1`, since the dotProduct differentiability API is not
derived in this file); (3) composition is done: the theorem packages both readouts
into `HasMarkLipschitzConstantsOn` for the actual kin/g from the pointwise
identifications.
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator NNReal

noncomputable section
namespace OTSelector.Reconstruction

/-- The linear probe: a linear functional of the shifted seed readout. -/
def linearProbe {E : Type*} {n : Type*} [Fintype n] (f : E → n → ℝ) (c b : n → ℝ) (d : ℝ) :
    E → ℝ :=
  fun e => (f e + c) ⬝ᵥ b + d

/-- **Linear-probe mark-Lipschitz transfer.**  If the shifted seed readout is C1 and
its linear probe is C1, then on a compact convex retained-root family the quadratic
kinetic readout and the linear probe have the mark-Lipschitz constants, given only
the pointwise identifications of the actual kin/g. -/
theorem hasMarkLipschitzConstantsOn_of_linearProbe {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) {n : Type*} [Fintype n]
    (f : E → n → ℝ) (c b : n → ℝ) (d : ℝ) (A : Matrix n n ℝ) {kin g : E → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hkin : ∀ e ∈ K, kin e = matrixQuadratic A (f e + c))
    (hg : ∀ e ∈ K, g e = linearProbe f c b d e)
    (hgC1 : ContDiff ℝ 1 (linearProbe f c b d)) :
    HasMarkLipschitzConstantsOn E K kin g := by
  have hq : ContDiff ℝ 1 (fun e : E => matrixQuadratic A (f e + c)) :=
    (contDiff_one_coefficientQuadratic A).comp (hf.add contDiff_const)
  obtain ⟨CA, hA⟩ := exists_hasBoundedFDerivOn_of_contDiff_one hK hne hq
  obtain ⟨CB, hB⟩ := exists_hasBoundedFDerivOn_of_contDiff_one hK hne hgC1
  obtain ⟨⟨Lk', hLk'⟩, ⟨Lg', hLg'⟩⟩ := hasMarkLipschitzConstantsOn_of_hasBoundedFDerivOn hconv hA hB
  constructor
  · refine ⟨Lk', hLk'.1, ?_⟩
    intro e he e' he'
    rw [hkin e he, hkin e' he']
    exact hLk'.2 e he e' he'
  · refine ⟨Lg', hLg'.1, ?_⟩
    intro e he e' he'
    rw [hg e he, hg e' he']
    exact hLg'.2 e he e' he'

end OTSelector.Reconstruction
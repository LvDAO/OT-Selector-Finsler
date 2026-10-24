import OTSelector.Reconstruction.FinslerOriginalMarkLipschitzLabelForm

/-!
# The mark-to-label C1 input, named exactly

The label-form transfer `hasMarkLipschitzConstantsOn_of_labelMap` needs
`ContDiff ℝ 1 lab` for the actual mark-to-label map on the compact mark class.  This
module names that input with its exact type and derives the consequence for the
actual lane.

IMPORTANT structural finding: in `FinslerCoefficientCoreLabel` the seed label map is
only established as MEASURABLE (`measurable_populationSeedRootLabelValue`) and
INJECTIVE in the extended form; no differentiability/smoothness of the
mark-to-label map is available in the repository data.  The C1 statement is
therefore a genuine geometric regularity assumption on the mark class: the label
section map (mark ↦ label vector in the seed covector coordinates) must be C1 on the
compact retained mark class — e.g. from the atlas/Ohta chart smoothness once the
section is expressed in chart coordinates.  It cannot be derived from the currently
formalized seed structure (measurability + injectivity only).
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator NNReal

noncomputable section
namespace OTSelector.Reconstruction

/-- The exact mark-to-label regularity input: the label map `lab` is C1. -/
def MarkToLabelC1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : Type*} [Fintype n] (lab : E → n → ℝ) : Prop :=
  ContDiff ℝ 1 lab

/-- The named input in its exact existential/universal form. -/
theorem markToLabelC1_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : Type*} [Fintype n] (lab : E → n → ℝ) : MarkToLabelC1 lab ↔ ContDiff ℝ 1 lab :=
  Iff.rfl

/-- **Wiring**: the named C1 input plus the pointwise identifications of the actual
kin/g with the frozen quadratic forms of the label map give the mark-Lipschitz
constants. -/
theorem hasMarkLipschitzConstantsOn_of_markToLabelC1 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) {n : Type*} [Fintype n]
    (lab : E → n → ℝ) (hlab : MarkToLabelC1 lab) (A B : Matrix n n ℝ)
    {kin g : E → ℝ}
    (hkin : ∀ e ∈ K, kin e = matrixQuadratic A (lab e))
    (hg : ∀ e ∈ K, g e = matrixQuadratic B (lab e)) :
    HasMarkLipschitzConstantsOn E K kin g :=
  hasMarkLipschitzConstantsOn_of_labelMap hK hne hconv lab hlab A B hkin hg

end OTSelector.Reconstruction
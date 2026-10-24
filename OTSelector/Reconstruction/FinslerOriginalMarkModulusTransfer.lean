import OTSelector.Reconstruction.FinslerOriginalSeedReadoutConcrete
import OTSelector.Reconstruction.FinslerOriginalMarkModulusCoupling

/-!
# Frozen mark-pairing identification and the mark modulus transfer

This module finishes the assembly of the mark lane.  It combines the concrete
population-seed label readout of `FinslerOriginalSeedReadoutConcrete` with the
mark-pairing identification of `FinslerOriginalKinPairingIdentification` and the
mark modulus transfer of `FinslerOriginalMarkModulusCoupling`.

Steps that are UNCONDITIONAL after the three named identification inputs:
- the concrete seed readout affineness on a chart parameter `Φ` gives the
  mark-Lipschitz constants for the concrete frozen quadratic kinetic/probe forms
  (`hasMarkLipschitzConstantsOn_of_parameterizedSeedReadoutAffine`);
- agreement of the ACTUAL kin/g with those quadratic readouts on the retained
  height-sliced roots transfers the constants to the actual kin/g
  (`hasMarkLipschitzConstantsOn_of_frozenMarkPairingIdentification` below);
- given the mark-Lipschitz constants and the mark modulus hypotheses, the marked
  edge error sum and mark rate limits follow from
  `sum_markedEdgeError_le_of_markModulus` and the mark rate tendsto lemmas
  (`FinslerOriginalMarkModulusCoupling`), i.e. the mark modulus transfer is
  complete modulo ONLY the coupling rate `ω → 0` and the constant-kernel
  reference limit as named hypotheses.

Named (not proved here) inputs: (i) `SeedReadoutParameterizedAffineOn` for the
concrete readout (seed window label/chart structure; `Z` is only a measurable
space, so affineness is on the chart parameter `Φ`); (ii) the two pairwise
identification equalities of the actual kin/g with the quadratic readouts, supplied
by the mark-pairing factorization `frozenPhysicalCost = matrixQuadratic
(C.matrix z₀ q) (label-difference readout)` on the height slice (`(u x, u y) = q`);
(iii) probe = linear/quadratic readout.
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator NNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

omit [BorelSpace E] in
/-- **Transfer of the mark-Lipschitz constants to the actual kin and g.**  If the
actual kinetic and probe functions agree on a compact convex retained-root family
(parametrized by the chart `Φ`) with the concrete frozen quadratic readouts, and the
concrete seed readout is affine there, then the actual kin and g have the
mark-Lipschitz constants — no Lipschitz constant is assumed. -/
theorem OriginalPopulationCoefficientCore.hasMarkLipschitzConstantsOn_of_frozenMarkPairingIdentification
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K) (Φ : E → Z)
    (A B : Matrix (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker))
      (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) ℝ)
    {kin g : E → ℝ}
    (haff : C.SeedReadoutParameterizedAffineOn Φ K)
    (hkin : ∀ e ∈ K, kin e = matrixQuadratic A (C.populationSeedReadout (Φ e)))
    (hg : ∀ e ∈ K, g e = matrixQuadratic B (C.populationSeedReadout (Φ e))) :
    HasMarkLipschitzConstantsOn E K kin g := by
  obtain ⟨⟨Lk', hLk'⟩, ⟨Lg', hLg'⟩⟩ :=
    C.hasMarkLipschitzConstantsOn_of_parameterizedSeedReadoutAffine hK hne hconv Φ A B haff
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

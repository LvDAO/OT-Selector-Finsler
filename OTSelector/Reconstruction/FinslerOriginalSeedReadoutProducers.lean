import OTSelector.Reconstruction.FinslerOriginalSeedReadoutIdentifications

/-!
# Producers: bounded-derivative (C1) readout variant

`FinslerOriginalSeedReadoutIdentifications` reduced the mark lane to three named
inputs, one of which required the concrete seed label readout to be AFFINE.  This
module proves the C1 alternative that the task asks for: if the seed readout is only
`ContDiff ℝ 1` (with continuous derivative) rather than affine, the frozen quadratic
compositions are still C1, the compact extraction gives `HasBoundedFDerivOn`, and
the mark-Lipschitz constants transfer to the ACTUAL kin and g.  So no affineness of
the labels is needed — C1 regularity suffices.

Status of the three inputs: (2) and (3) are reduced here to the pointwise readout
equalities (proved definitionally by the height-slice pairing factorization of
`FinslerOriginalKinPairingIdentification` once the Φ-parameterized mark is matched
with the two-mark readout); (1) is replaced by the strictly weaker C1 hypothesis
`ContDiff ℝ 1 f` on the readout, which is what a differentiable label/chart data
yields.  Remaining exact inputs: `ContDiff ℝ 1` of the concrete readout along Φ, and
the pointwise identification equalities.
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator NNReal

noncomputable section
namespace OTSelector.Reconstruction

/-- **C1 readout variant of the mark-Lipschitz transfer.**  If the seed label
readout `f : E → (n → ℝ)` is C1 on the (chart-parameterized) retained roots and the
actual kin/g agree there with the frozen quadratic forms of `f`, then kin and g have
the mark-Lipschitz constants — with no affineness and no Lipschitz constant assumed. -/
theorem hasMarkLipschitzConstantsOn_of_contDiff_readouts {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) {n : Type*} [Fintype n]
    {f : E → n → ℝ} (hf : ContDiff ℝ 1 f) {A B : Matrix n n ℝ} {kin g : E → ℝ}
    (hkin : ∀ e ∈ K, kin e = matrixQuadratic A (f e))
    (hg : ∀ e ∈ K, g e = matrixQuadratic B (f e)) :
    HasMarkLipschitzConstantsOn E K kin g := by
  have hqA : ContDiff ℝ 1 (fun e : E => matrixQuadratic A (f e)) :=
    (contDiff_one_coefficientQuadratic A).comp hf
  have hqB : ContDiff ℝ 1 (fun e : E => matrixQuadratic B (f e)) :=
    (contDiff_one_coefficientQuadratic B).comp hf
  obtain ⟨CA, hA⟩ := exists_hasBoundedFDerivOn_of_contDiff_one hK hne hqA
  obtain ⟨CB, hB⟩ := exists_hasBoundedFDerivOn_of_contDiff_one hK hne hqB
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
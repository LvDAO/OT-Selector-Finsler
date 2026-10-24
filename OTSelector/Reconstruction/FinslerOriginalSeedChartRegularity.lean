import OTSelector.Reconstruction.FinslerOriginalSeedReadoutRegularity

/-!
# Seed chart regularity: C1 of the linear probe

This module proves the C1 regularity of the linear probe from C1 of the seed readout:
the finite dotProduct is a finite sum of products, so composing the C1 projection
coordinates with the C1 readout keeps C1.  This closes the `hgC1` input of
`hasMarkLipschitzConstantsOn_of_linearProbe`, leaving only the chart regularity of
the concrete label readout and the lane's pointwise identifications as named inputs.
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator NNReal

noncomputable section
namespace OTSelector.Reconstruction

/-- C1 of the linear probe from C1 of the seed readout. -/
theorem contDiff_one_linearProbe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : Type*} [Fintype n] {f : E → n → ℝ} (hf : ContDiff ℝ 1 f)
    (c b : n → ℝ) (d : ℝ) : ContDiff ℝ 1 (linearProbe f c b d) := by
  have hfun : linearProbe f c b d =
      fun e : E => (∑ i, (f e + c) i * b i) + d := by
    funext e
    simp [linearProbe, dotProduct]
  rw [hfun]
  fun_prop

end OTSelector.Reconstruction

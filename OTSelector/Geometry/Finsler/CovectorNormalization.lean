import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCovectorNormalization.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCovectorNormalization`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CovectorNormalization

* **Conditions:** A supplied genuine smooth inverse Legendre branch and a prescribed strictly positive target energy.
* **Objects:** An explicit positive square-root covector normalization smooth on the entire inverse target, remaining in the original slit domain with exactly the target energy.
* **Proof detail:** Scale the actual inverse velocity by sqrt(target/current energy), use energy homogeneity and read its momentum by degree-one Legendre scaling.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): The scaled state need only remain in the slit domain; it is not unnecessarily required to stay in the supplied inverse branch source.
-/

/-!
# Explicit covector normalization on the entire supplied inverse branch

Positive square-root rescaling normalizes the actual inverse-Legendre energy to
one prescribed positive value. The resulting state remains in the original slit
chart domain, which is sufficient to feed the supplied all-slit complete flow.
There is no unnecessary requirement that the scaled state stay in the inverse
branch source, and no new branch or flow is selected.
-/

open Set Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The positive scale determined by the actual inverse-Legendre energy. -/
def covectorNormalizationScale (F : ContinuousFinslerNorm E M) (old : M)
    (eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))) (c : ℝ)
    (q : E × (E →L[ℝ] ℝ)) : ℝ :=
  Real.sqrt (c / F.chartEnergy old (eL.symm q))

/-- The same inverse branch, with its velocity positively rescaled. -/
def covectorNormalization (F : ContinuousFinslerNorm E M) (old : M)
    (eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))) (c : ℝ)
    (q : E × (E →L[ℝ] ℝ)) : E × E :=
  (q.1, F.covectorNormalizationScale old eL c q • (eL.symm q).2)

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- The explicit normalization is smooth on the entire inverse target. Its actual
energy is `c`, its momentum is the original covector scaled by the positive
factor, and it fixes inverse states whose energy already equals `c`. -/
theorem covectorNormalization_spec (hF : F.IsSmoothStronglyConvex) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {c : ℝ} (hc : 0 < c) :
    ContDiffOn ℝ ∞ (F.covectorNormalizationScale old eL c) eL.target ∧
      ContDiffOn ℝ ∞ (F.covectorNormalization old eL c) eL.target ∧
      ∀ q ∈ eL.target,
        0 < F.covectorNormalizationScale old eL c q ∧
        F.covectorNormalization old eL c q ∈ chartEnergyDomain old ∧
        F.chartEnergy old (F.covectorNormalization old eL c q) = c ∧
        fiberLegendre (F.chartEnergy old) (F.covectorNormalization old eL c q) =
          F.covectorNormalizationScale old eL c q • q.2 ∧
        (F.chartEnergy old (eL.symm q) = c →
          F.covectorNormalization old eL c q = eL.symm q) := by
  have hdomain (q) (hq : q ∈ eL.target) : eL.symm q ∈ chartEnergyDomain old :=
    hsource (eL.map_target hq)
  have hpos (q) (hq : q ∈ eL.target) : 0 < F.chartEnergy old (eL.symm q) :=
    F.chartEnergy_pos old (hdomain q hq)
  have henergy : ContDiffOn ℝ ∞ (fun q ↦ F.chartEnergy old (eL.symm q)) eL.target :=
    (hF.contDiffOn_chartEnergy old).comp hInv hdomain
  have hscale : ContDiffOn ℝ ∞ (F.covectorNormalizationScale old eL c) eL.target :=
    (contDiffOn_const.div henergy (fun q hq ↦ (hpos q hq).ne')).sqrt
      (fun q hq ↦ (div_pos hc (hpos q hq)).ne')
  refine ⟨hscale, contDiffOn_fst.prodMk (hscale.smul hInv.snd), ?_⟩
  intro q hq
  have hi := parametricLegendre_inverse_components heL hq
  have heq : eL.symm q = (q.1, (eL.symm q).2) := Prod.ext hi.1 rfl
  have hm : (q.1, (eL.symm q).2) ∈ chartEnergyDomain old := by
    rw [← heq]
    exact hdomain q hq
  have ha : 0 < F.covectorNormalizationScale old eL c q :=
    Real.sqrt_pos.2 (div_pos hc (hpos q hq))
  refine ⟨ha, ⟨hm.1, smul_ne_zero ha.ne' hm.2⟩, ?_, ?_, ?_⟩
  · unfold covectorNormalization
    rw [F.chartEnergy_smul old hm.1, ← heq]
    change (Real.sqrt (c / F.chartEnergy old (eL.symm q))) ^ 2 *
      F.chartEnergy old (eL.symm q) = c
    rw [Real.sq_sqrt (div_pos hc (hpos q hq)).le]
    exact div_mul_cancel₀ _ (hpos q hq).ne'
  · unfold covectorNormalization
    rw [hF.chartLegendre_pos_smul old hm.1 hm.2 ha, ← heq, hi.2]
  · intro hfixed
    have haone : F.covectorNormalizationScale old eL c q = 1 := by
      unfold covectorNormalizationScale
      rw [hfixed, div_self hc.ne', Real.sqrt_one]
    simpa only [covectorNormalization, haone, one_smul] using heq.symm

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end

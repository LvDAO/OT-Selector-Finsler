import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.LegendreInjectivity

/-!
# Geometry.Finsler.MeasurableLegendre

* **Conditions:** Smooth strong convexity on the actual slit chart domain and its already proved nonlinear Legendre injectivity.
* **Objects:** A Borel embedding/equivalence with the actual Legendre range and measurable recovered original velocity, including measurable-parameter composition.
* **Proof detail:** Use slit smoothness and injectivity for Lusin–Souslin, invert the Borel range equivalence and read the exact original base/covector identities.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.

Source relation (derived): No measurable inverse-branch selection or nonempty-domain assumption is introduced.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerMeasurableLegendre.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerMeasurableLegendre`; the selected original proof blocks follow. -/
section

/-!
# An actual measurable inverse of the chart Legendre map

On the original slit chart domain, smoothness and nonlinear Legendre injectivity give
an actual measurable embedding. Its equivalence with its measurable range supplies a
measurable inverse without a nonempty-domain assumption or a branch-selection oracle.
The inverse retains the base point and recovers the actual fiber differential. Composing
with any measurable phase map gives measurable recovered velocities on its valid domain.
-/

open Set MeasureTheory Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The genuine joint Legendre map restricted to the original slit chart domain. -/
def chartLegendreOnSlit (F : ContinuousFinslerNorm E M) (old : M) :
    chartEnergyDomain (E := E) old → E × (E →L[ℝ] ℝ) :=
  (chartEnergyDomain (E := E) old).domRestrict (parametricLegendre (F.chartEnergy old))

/-- The actual image of the slit chart Legendre map, with no surjectivity assumption. -/
def chartLegendreRange (F : ContinuousFinslerNorm E M) (old : M) : Set (E × (E →L[ℝ] ℝ)) :=
  range (F.chartLegendreOnSlit old)

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)

include hF

/-- The actual Legendre map on its entire slit chart domain is a measurable embedding. -/
theorem measurableEmbedding_chartLegendreOnSlit (old : M) :
    MeasurableEmbedding (F.chartLegendreOnSlit old) := by
  apply ContinuousOn.measurableEmbedding (isOpen_chartEnergyDomain (E := E) old).measurableSet
    _ (hF.injOn_parametricLegendre_chartEnergy old)
  intro z hz
  exact (contDiffAt_parametricLegendre ((hF.contDiffOn_chartEnergy old).contDiffAt
    ((isOpen_chartEnergyDomain (E := E) old).mem_nhds hz))).continuousAt.continuousWithinAt

/-- The actual image is measurable in the ordinary base-covector Borel space. -/
theorem measurableSet_chartLegendreRange (old : M) :
    MeasurableSet (F.chartLegendreRange old) :=
  (hF.measurableEmbedding_chartLegendreOnSlit old).measurableSet_range

/-- The actual measurable Legendre inverse is obtained on the actual range, even if empty. -/
def chartLegendreEquivRange (old : M) :
    chartEnergyDomain (E := E) old ≃ᵐ F.chartLegendreRange old :=
  (hF.measurableEmbedding_chartLegendreOnSlit old).equivRange

/-- The measurable equivalence is the original nonlinear Legendre map, not a new coordinate map. -/
theorem chartLegendreEquivRange_apply_val (old : M) (z : chartEnergyDomain (E := E) old) :
    (hF.chartLegendreEquivRange old z).val = parametricLegendre (F.chartEnergy old) z.val := by
  exact congrArg Subtype.val
    ((hF.measurableEmbedding_chartLegendreOnSlit old).equivRange_apply z)

/-- The constructed inverse recovers every original slit phase from its actual forward image. -/
theorem chartLegendreEquivRange_symm_forward (old : M) (z : chartEnergyDomain (E := E) old) :
    (hF.chartLegendreEquivRange old).symm
      ⟨F.chartLegendreOnSlit old z, mem_range_self z⟩ = z :=
  (hF.measurableEmbedding_chartLegendreOnSlit old).equivRange_symm_apply_mk z

/-- Applying the original Legendre map to the recovered phase gives the original momentum. -/
theorem parametricLegendre_chartLegendreEquivRange_symm (old : M)
    (p : F.chartLegendreRange old) :
    parametricLegendre (F.chartEnergy old)
      ((hF.chartLegendreEquivRange old).symm p).val = p.val := by
  rw [← hF.chartLegendreEquivRange_apply_val]
  exact congrArg Subtype.val ((hF.chartLegendreEquivRange old).apply_symm_apply p)

/-- The inverse keeps the base coordinate and has the actual prescribed vertical differential. -/
theorem chartLegendreEquivRange_symm_components (old : M) (p : F.chartLegendreRange old) :
    ((hF.chartLegendreEquivRange old).symm p).val.1 = p.val.1 ∧
      fiberLegendre (F.chartEnergy old) ((hF.chartLegendreEquivRange old).symm p).val =
        p.val.2 ∧ ((hF.chartLegendreEquivRange old).symm p).val.2 ≠ 0 := by
  have h := hF.parametricLegendre_chartLegendreEquivRange_symm old p
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h,
    ((hF.chartLegendreEquivRange old).symm p).property.2⟩

/-- The recovered actual velocity is measurable on the entire actual range. -/
theorem measurable_chartLegendre_inverseVelocity (old : M) :
    Measurable (fun p : F.chartLegendreRange old ↦
      ((hF.chartLegendreEquivRange old).symm p).val.2) :=
  measurable_snd.comp (measurable_subtype_coe.comp
    (hF.chartLegendreEquivRange old).symm.measurable)

/-- For any measurable phase data, the set on which the actual inverse exists is measurable. -/
theorem measurableSet_chartLegendre_valid {A : Type*} [MeasurableSpace A]
    (old : M) {p : A → E × (E →L[ℝ] ℝ)} (hp : Measurable p) :
    MeasurableSet (p ⁻¹' F.chartLegendreRange old) :=
  (hF.measurableSet_chartLegendreRange old).preimage hp

/-- Measurable phase data give measurable actual inverse phases on their valid subtype. -/
theorem measurable_chartLegendre_inverse_comp {A : Type*} [MeasurableSpace A]
    (old : M) {p : A → E × (E →L[ℝ] ℝ)} (hp : Measurable p) :
    Measurable (fun a : p ⁻¹' F.chartLegendreRange old ↦
      ((hF.chartLegendreEquivRange old).symm ⟨p a.val, a.property⟩).val) :=
  measurable_subtype_coe.comp ((hF.chartLegendreEquivRange old).symm.measurable.comp
    (hp.comp measurable_subtype_coe).subtype_mk)

/-- In particular, the velocity recovered from arbitrary valid measurable data is measurable. -/
theorem measurable_chartLegendre_inverseVelocity_comp {A : Type*} [MeasurableSpace A]
    (old : M) {p : A → E × (E →L[ℝ] ℝ)} (hp : Measurable p) :
    Measurable (fun a : p ⁻¹' F.chartLegendreRange old ↦
      ((hF.chartLegendreEquivRange old).symm ⟨p a.val, a.property⟩).val.2) :=
  measurable_snd.comp (hF.measurable_chartLegendre_inverse_comp old hp)

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end

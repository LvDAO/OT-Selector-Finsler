import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
## Lemma skeleton

* **Conditions:** A Borel label region V, maps continuous relative to V, closed core K and two prescribed scalar endpoint values; a real open time interval for the product-window result.
* **Objects:** A relatively closed label subtype event, its ambient measurable label event and its measurable time-product window.
* **Proof detail:** Take closed preimages and equality sets inside the V subtype, then use its measurable inclusion and product measurability.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4, Appendix*, Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
  https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32

**Relationship to the sources:** Elementary relative-continuity and Borel-subspace construction. Arbitrary extensions outside V need not be measurable; no calibration/geodesic theorem is invoked.
-/

/-!
# Measurable calibration windows from relative continuity

Closed core membership and two endpoint equalities form a relatively closed label
set. On a Borel label domain this gives a Borel time window without any measurability
requirement on arbitrary extensions outside the label domain.
-/

open Set

namespace OTSelector.Geometry

variable {W E : Type*} [TopologicalSpace W] [TopologicalSpace E]
  {V : Set W} {K : Set E} {σ : W → E} {f g : W → ℝ} {c d : ℝ}

/-- Core membership and two endpoint equalities are closed in the original label subtype. -/
theorem isClosed_calibratedWindow_labelSubtype
    (hσ : ContinuousOn σ V) (hK : IsClosed K)
    (hf : ContinuousOn f V) (hg : ContinuousOn g V) :
    IsClosed {w : V | σ w ∈ K ∧ f w = c ∧ g w = d} := by
  have hσV : Continuous (fun w : V ↦ σ w) :=
    continuousOn_iff_continuous_domRestrict.mp hσ
  have hfV : Continuous (fun w : V ↦ f w) :=
    continuousOn_iff_continuous_domRestrict.mp hf
  have hgV : Continuous (fun w : V ↦ g w) :=
    continuousOn_iff_continuous_domRestrict.mp hg
  exact (hK.preimage hσV).inter
    ((isClosed_eq hfV continuous_const).inter (isClosed_eq hgV continuous_const))

variable [MeasurableSpace W] [BorelSpace W]

/-- A Borel label domain and relative continuity make the screened core labels Borel. -/
theorem measurableSet_calibratedWindow_labels
    (hV : MeasurableSet V) (hσ : ContinuousOn σ V) (hK : IsClosed K)
    (hf : ContinuousOn f V) (hg : ContinuousOn g V) :
    MeasurableSet (V ∩ σ ⁻¹' K ∩ {w | f w = c} ∩ {w | g w = d}) := by
  have hc := isClosed_calibratedWindow_labelSubtype (c := c) (d := d) hσ hK hf hg
  have heq : V ∩ σ ⁻¹' K ∩ {w | f w = c} ∩ {w | g w = d} =
      ((↑) : V → W) '' {w : V | σ w ∈ K ∧ f w = c ∧ g w = d} := by
    ext w
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_image, Subtype.exists]
    aesop
  rw [heq]
  exact (MeasurableEmbedding.subtype_coe hV).measurableSet_image.mpr hc.measurableSet

/-- The open time interval times the calibration-screened core labels is Borel. -/
theorem measurableSet_calibratedWindow
    (hV : MeasurableSet V) (hσ : ContinuousOn σ V) (hK : IsClosed K)
    (hf : ContinuousOn f V) (hg : ContinuousOn g V) (a b : ℝ) :
    MeasurableSet (Ioo a b ×ˢ (V ∩ σ ⁻¹' K ∩ {w | f w = c} ∩ {w | g w = d})) :=
  isOpen_Ioo.measurableSet.prod (measurableSet_calibratedWindow_labels hV hσ hK hf hg)

end OTSelector.Geometry

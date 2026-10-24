import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
## Lemma skeleton

* **Conditions:** Measurable label and scalar maps; local joint laws are absolutely continuous relative to their own label marginals times volume on a countable cover, or on positive-radius neighborhoods of a compact set.
* **Objects:** Joint label-scalar absolute continuity on the whole covered set.
* **Proof detail:** A global reference-null set is null for every local marginal by monotonicity. Local joint absolute continuity and the countable cover give global nullity; compactness supplies a finite/countable subcover.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf
* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 251A–251I, pp. 2–6: rectangular covers, product outer measures and the product-measure rectangle formula.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=2
* Jiří Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I*, Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).
  https://www.jirka.org/ra/html/sec_metcont.html

**Relationship to the sources:** Elementary localization of absolute continuity and product-measure monotonicity. A single uniform radius or positive lower density is not introduced.
-/

/-!
# Local-to-global absolute continuity of label and scalar coordinates

Absolute continuity against the actual label marginal times scalar volume passes
from countably many overlapping pieces to their cover. Compact sets need only local
closed-ball pieces; no uniform radius or lower bound on a population density is used.
-/

open Set MeasureTheory Metric
open scoped ENNReal

namespace OTSelector.Reconstruction

variable {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]

/-- Countably many overlapping pieces with scalar absolute continuity give the same
property on their cover, relative to the original cover's own label marginal. -/
theorem map_label_clock_absolutelyContinuous_of_countable_cover
    (ν : Measure M) {a : M → Z} {u : M → ℝ}
    (ha : Measurable a) (hu : Measurable u)
    {ι : Type*} [Countable ι] {K : ι → Set M} {S : Set M}
    (hsub : ∀ i, K i ⊆ S) (hcover : S ⊆ ⋃ i, K i)
    (hlocal : ∀ i, ((ν.restrict (K i)).map (fun x ↦ (a x, u x))) ≪
      ((ν.restrict (K i)).map a).prod volume) :
    ((ν.restrict S).map (fun x ↦ (a x, u x))) ≪
      ((ν.restrict S).map a).prod volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro B hB hnull
  have hpair : Measurable (fun x ↦ (a x, u x)) := ha.prodMk hu
  have hpre : MeasurableSet ((fun x ↦ (a x, u x)) ⁻¹' B) := hpair hB
  have hpiece (i : ι) : ν ((fun x ↦ (a x, u x)) ⁻¹' B ∩ K i) = 0 := by
    have hlabel := Measure.map_mono (Measure.restrict_mono_set ν (hsub i)) ha
    have hprod := Measure.prod_mono hlabel (le_refl (volume : Measure ℝ))
    have hn := hlocal i (hprod.absolutelyContinuous hnull)
    simpa only [Measure.map_apply hpair hB, Measure.restrict_apply hpre] using hn
  rw [Measure.map_apply hpair hB, Measure.restrict_apply hpre]
  apply measure_mono_null _ (measure_iUnion_null hpiece)
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx.2)
  exact mem_iUnion.mpr ⟨i, hx.1, hi⟩

/-- Local scalar absolute continuity on closed-ball pieces of a compact set gives
absolute continuity on the whole set. The finite subcover and radii are constructed. -/
theorem map_label_clock_absolutelyContinuous_of_compact_local
    [PseudoMetricSpace M] (ν : Measure M) {a : M → Z} {u : M → ℝ}
    (ha : Measurable a) (hu : Measurable u) {K : Set M} (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧
      ((ν.restrict (K ∩ closedBall x r)).map (fun y ↦ (a y, u y))) ≪
        ((ν.restrict (K ∩ closedBall x r)).map a).prod volume) :
    ((ν.restrict K).map (fun x ↦ (a x, u x))) ≪
      ((ν.restrict K).map a).prod volume := by
  classical
  have hloc (x : K) := hlocal x x.property
  choose r hr hac using hloc
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover (fun x : K ↦ ball (x : M) (r x))
    (fun _ ↦ isOpen_ball) (fun x hx ↦ mem_iUnion.mpr
      ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩)
  let P (j : {x // x ∈ J}) : Set M := K ∩ closedBall (j.val : M) (r j.val)
  apply map_label_clock_absolutelyContinuous_of_countable_cover ν ha hu
    (K := P) (fun _ ↦ inter_subset_left) ?_ (fun j ↦ hac j.val)
  intro x hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hJ hx)
  exact mem_iUnion.mpr ⟨⟨j, hj⟩, hx, ball_subset_closedBall hxj⟩

end OTSelector.Reconstruction

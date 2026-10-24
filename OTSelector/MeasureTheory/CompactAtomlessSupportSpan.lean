import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.Order.Compact

/-!
## Lemma skeleton

* **Conditions:** A nonzero real Borel measure with null singletons and compact support; no finite-mass assumption is imposed.
* **Objects:** Distinct support endpoints a<b carrying the whole law in their open interval.
* **Proof detail:** Take the minimum and maximum of the nonempty compact support. If they coincide the measure is concentrated on one null singleton, contradicting nonzero mass. Remove the two null endpoints from the full-mass closed support interval.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 411N(a)–(d), p. 6: self-supporting sets and the unique full-measure closed support.
  https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=6
* Jiří Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I*, Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).
  https://www.jirka.org/ra/html/sec_metcont.html

**Relationship to the sources:** Compact-extrema and support-null-complement corollary. Compact support with singleton-nullness does not itself assert finite total mass.
-/

/-!
# Finite endpoints of an atomless compact scalar law

The endpoints belong to the actual measure support. Removing those two points
loses no mass, so the entire law is carried by the resulting open interval.
-/

open Set Filter MeasureTheory

namespace OTSelector.Geometry

/-- A nonzero atomless scalar measure with compact support has distinct attained
endpoints and gives full mass to the open interval between them. -/
theorem exists_compact_measure_clock_span (μ : Measure ℝ) [NullSingletonClass μ]
    (hμ : μ ≠ 0) (hcompact : IsCompact μ.support) :
    ∃ a b : ℝ, a ∈ μ.support ∧ b ∈ μ.support ∧ a < b ∧
      μ.support ⊆ Icc a b ∧ ∀ᵐ t ∂μ, t ∈ Ioo a b := by
  let a := sInf μ.support
  let b := sSup μ.support
  have hnonempty := μ.nonempty_support hμ
  have ha : a ∈ μ.support := hcompact.sInf_mem hnonempty
  have hb : b ∈ μ.support := hcompact.sSup_mem hnonempty
  have hbound : μ.support ⊆ Icc a b := fun t ht ↦
    ⟨csInf_le hcompact.bddBelow ht, le_csSup hcompact.bddAbove ht⟩
  have hinside : ∀ᵐ t ∂μ, t ∈ Ioo a b := by
    filter_upwards [μ.support_mem_ae, μ.ae_ne a, μ.ae_ne b] with t ht hta htb
    exact ⟨lt_of_le_of_ne (hbound ht).1 hta.symm, lt_of_le_of_ne (hbound ht).2 htb⟩
  have hab : a < b := by
    let : (ae μ).NeBot := ae_neBot.mpr hμ
    obtain ⟨t, ht⟩ := hinside.exists
    exact ht.1.trans ht.2
  exact ⟨a, b, ha, hb, hab, hbound, hinside⟩

end OTSelector.Geometry

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
## Lemma skeleton

* **Conditions:** A locally compact second-countable Hausdorff carrier, compact J and closed exceptional S; the mass conclusion additionally assumes finite mass of J and null S.
* **Objects:** Monotone compact exhaustion of J minus S eventually capturing every compact regular subset, and discarded mass tending to zero.
* **Proof detail:** Exhaust the open complement of S by compact sets whose interiors cover it, intersect with J, and use compactness to capture every regular compact subset. Apply continuity from above to J minus K_n.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4, Appendix*, Sections 4A2G(e), pp. 15–16; 4A2N(b), p. 22; 4A2Q(h) and proof, pp. 24–25.
  https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=24
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 2B, Theorems 2.59–2.60, p. 44 (increasing and decreasing sets).
  https://measure.axler.net/MIRA.pdf#page=59

**Relationship to the sources:** Derived topological compact-exhaustion construction and finite-measure continuity. No convergence rate or measurable chart choice is assumed.
-/

/-!
# Compact localization away from a closed exceptional set

A countable monotone family of compact sets covers the regular part of a compact set
and eventually contains every compact regular subset. If the exceptional set is null,
the discarded original mass tends to zero. No rate or measurable choice of local charts
is assumed. This supplies compact localization after finite focal times are removed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [SecondCountableTopology X]

/-- Construct compact regular sets exhausting a compact set minus a closed exceptional
set. Every compact regular subset is contained in one member of the same exhaustion. -/
theorem exists_compact_exhaustion_sdiff_closed {J S : Set X}
    (hJ : IsCompact J) (hS : IsClosed S) :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ Monotone K ∧
      (∀ n, K n ⊆ J \ S) ∧ (⋃ n, K n) = J \ S ∧
      ∀ L : Set X, IsCompact L → L ⊆ J \ S → ∃ n, L ⊆ K n := by
  let U := Sᶜ
  have hU : IsOpen U := hS.isOpen_compl
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  let C : CompactExhaustion U := CompactExhaustion.choice U
  let K : ℕ → Set X := fun n ↦ J ∩ Subtype.val '' C n
  have hc (n : ℕ) : IsCompact (K n) :=
    hJ.inter ((C.isCompact n).image continuous_subtype_val)
  have hm : Monotone K := fun _ _ h ↦ inter_subset_inter_right _ (image_mono (C.subset h))
  have hs (n : ℕ) : K n ⊆ J \ S := by
    rintro x ⟨hxJ, u, hu, rfl⟩
    exact ⟨hxJ, u.property⟩
  have hu : (⋃ n, K n) = J \ S := by
    apply Subset.antisymm (iUnion_subset hs)
    intro x hx
    obtain ⟨n, hn⟩ := C.exists_mem ⟨x, hx.2⟩
    exact mem_iUnion.mpr ⟨n, hx.1, ⟨x, hx.2⟩, hn, rfl⟩
  refine ⟨K, hc, hm, hs, hu, ?_⟩
  intro L hL hLS
  have himage : Subtype.val '' ((Subtype.val : U → X) ⁻¹' L) = L := by
    apply Subset.antisymm
    · rintro x ⟨u, hu, rfl⟩
      exact hu
    · intro x hx
      exact ⟨⟨x, (hLS hx).2⟩, hx, rfl⟩
  have hLc : IsCompact ((Subtype.val : U → X) ⁻¹' L) :=
    Subtype.isCompact_iff.mpr (by rw [himage]; exact hL)
  obtain ⟨n, hn⟩ := C.exists_superset_of_isCompact hLc
  refine ⟨n, ?_⟩
  intro x hx
  exact ⟨(hLS hx).1, ⟨x, (hLS hx).2⟩, hn hx, rfl⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- Compact localization discards asymptotically zero original mass when the closed
exceptional set is null. Finite mass is needed only on the selected compact set. -/
theorem exists_compact_exhaustion_sdiff_null (μ : Measure X) {J S : Set X}
    (hJ : IsCompact J) (hS : IsClosed S) (hμJ : μ J ≠ ∞) (hμS : μ S = 0) :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ Monotone K ∧
      (∀ n, K n ⊆ J \ S) ∧ (⋃ n, K n) = J \ S ∧
      (∀ L : Set X, IsCompact L → L ⊆ J \ S → ∃ n, L ⊆ K n) ∧
      Tendsto (fun n ↦ μ (J \ K n)) atTop (𝓝 0) := by
  obtain ⟨K, hc, hm, hs, hu, hcapture⟩ := exists_compact_exhaustion_sdiff_closed hJ hS
  have hmeas (n : ℕ) : NullMeasurableSet (J \ K n) μ :=
    (hJ.isClosed.measurableSet.diff (hc n).isClosed.measurableSet).nullMeasurableSet
  have ha : Antitone (fun n ↦ J \ K n) := fun _ _ h ↦ sdiff_subset_sdiff_right (hm h)
  have hfin : ∃ n, μ (J \ K n) ≠ ∞ :=
    ⟨0, ne_top_of_le_ne_top hμJ (measure_mono sdiff_subset)⟩
  have hI : (⋂ n, J \ K n) = J ∩ S := by
    rw [← sdiff_iUnion, hu]
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  have hzero : μ (J ∩ S) = 0 := measure_mono_null inter_subset_right hμS
  have ht := tendsto_measure_iInter_atTop hmeas ha hfin
  rw [hI, hzero] at ht
  exact ⟨K, hc, hm, hs, hu, hcapture, ht⟩

end OTSelector.Geometry

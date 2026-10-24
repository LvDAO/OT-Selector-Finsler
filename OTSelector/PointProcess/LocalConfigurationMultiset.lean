import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Multiset.Sort
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Group.Arithmetic
import OTSelector.MeasureTheory.FiniteMultisetEncoding
import OTSelector.PointProcess.FinitePointCloud

/-!
Conditions: Standard-Borel measurable point/target spaces for multiset maps; measurable additive commutative targets for sums, and arbitrary measurable external parameters for parameterized sums.

Objects: Canonical finite-cloud enumeration of multisets, measurable atomwise pushforward, finite observable sums and jointly measurable parameterized sums.

Proof detail: Read the sorted multiset code as a finite cloud and use its measurable order-forgetting inverse. Split padded-code sums by their natural length and apply measurable finite addition, retaining each external parameter.

References: D. H. Fremlin: 424B(b–d), 424C–D, pp. 30–31; 424G, p. 31; Günter Last; Mathew Penrose: Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10.
Relation: Concrete coding and measurable algebra generalizing real counting integrals to arbitrary measurable additive-monoid targets. No compatible point order is presumed.
-/


/-!
## Lemma skeleton

* **Conditions:** X is a measurable standard-Borel point space with the library sorted-code multiset measurable structure. Measurability of Multiset.map f additionally requires a measurable standard-Borel target Y and measurable f. For sums, Y may instead be any additively commutative monoid with a measurable space and measurable binary addition. The parameterized sum permits any measurable parameter space A and a jointly measurable observable f : A x X -> Y.
* **Objects:** toFinitePointCloud: canonical measurable enumeration of a multiset by its chosen real coding order; codeSum: finite fold of an observable over the padded finite code; Multiset.map: pushforward of every atom, retaining its multiplicity; sum_map_param: sum of a jointly measurable point observable while preserving an external parameter
* **Proof detail:** Read the already-sorted multiset code as a finite ordered cloud. Use the cloud padded-code measurability and the exact order-forgetting inverse. Factor multiset pushforward through canonical enumeration, cloud mapping and measurable order-forgetting. Express sums as a finite option-code sum, split over the natural length, and use measurability of finite sums and addition; retain the parameter in the product carrier.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31.
  https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30
* Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*, Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10.
  https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22

**Relationship to the sources:** The canonical enumeration is a standard-Borel coding choice. Mapping and finite sums are measurable algebraic consequences; arbitrary measurable additive-monoid targets and external parameters generalize the real-valued counting-integral formula.
-/

/-!
# Measurable finite-multiset operations for local configurations

The sorted code of a multiset gives a measurable ordered finite cloud.  The existing cloud map
and unordered projection then prove measurability of multiset pushforward without imposing an
order compatible with a topology on the point space.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace OTSelector.PointProcess.MultisetEncoding

variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]

/-- Read the canonical measurable ordering as an ordinary finite cloud. -/
noncomputable def toFinitePointCloud (m : Multiset X) : FinitePointCloud X where
  card := m.card
  point i := (m.sort (codingLE X))[i.val]'(by simp)

@[simp]
theorem paddedCode_toFinitePointCloud (m : Multiset X) :
    FinitePointCloud.paddedCode (toFinitePointCloud m) = paddedCode m := by
  apply Prod.ext
  · rfl
  · funext k
    change (if hk : k < m.card then
      some ((m.sort (codingLE X))[k]'(by simpa using hk)) else none) =
      (m.sort (codingLE X))[k]?
    by_cases hk : k < m.card
    · simp [hk]
    · simp [hk]

/-- Canonical enumeration is measurable through its padded code. -/
@[fun_prop]
theorem measurable_toFinitePointCloud :
    Measurable (toFinitePointCloud : Multiset X → FinitePointCloud X) := by
  rw [measurable_comap_iff]
  simpa only [Function.comp_def, paddedCode_toFinitePointCloud] using
    (measurable_paddedCode (X := X))

@[simp]
theorem toMultiset_toFinitePointCloud (m : Multiset X) :
    (toFinitePointCloud m).toMultiset = m := by
  have hlist : (toFinitePointCloud m).toList = m.sort (codingLE X) := by
    apply List.ext_get
    · simp [toFinitePointCloud]
    · intro k hk hl
      simp [FinitePointCloud.toList, toFinitePointCloud]
  simpa only [FinitePointCloud.toMultiset, hlist] using Multiset.sort_eq m (codingLE X)

/-- A measurable point map induces a measurable pushforward on finite multisets. -/
@[fun_prop]
theorem measurable_map [MeasurableSpace Y] [StandardBorelSpace Y] {f : X → Y}
    (hf : Measurable f) : Measurable (Multiset.map f : Multiset X → Multiset Y) := by
  have h := FinitePointCloud.measurable_toMultiset.comp
    ((FinitePointCloud.measurable_map hf).comp measurable_toFinitePointCloud)
  simpa only [Function.comp_def, FinitePointCloud.toMultiset_map,
    toMultiset_toFinitePointCloud] using h

section Sums

variable [AddCommMonoid Y] [MeasurableSpace Y] [MeasurableAdd₂ Y]

private def codeSum (f : X → Y) (code : FinitePointCloud.PaddedCode X) : Y :=
  ∑ k ∈ Finset.range code.1, (code.2 k).elim 0 f

omit [StandardBorelSpace X] in
private theorem measurable_codeSum {f : X → Y} (hf : Measurable f) :
    Measurable (codeSum f) := by
  have hsum : Measurable (fun p : FinitePointCloud.PaddedCode X × ℕ ↦
      ∑ k ∈ Finset.range p.2, (p.1.2 k).elim 0 f) := by
    apply measurable_from_prod_countable_left
    intro n
    change Measurable (fun code : FinitePointCloud.PaddedCode X ↦
      ∑ k ∈ Finset.range n, (code.2 k).elim 0 f)
    apply Finset.measurable_sum
    intro k hk
    exact (MeasureTheory.Option.measurable_elim 0 hf).comp
      ((measurable_pi_apply k).comp measurable_snd)
  exact hsum.comp (measurable_id.prodMk measurable_fst)

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [MeasurableAdd₂ Y] in
private theorem codeSum_paddedCode_cloud (f : X → Y) (cloud : FinitePointCloud X) :
    codeSum f (FinitePointCloud.paddedCode cloud) = (cloud.toMultiset.map f).sum := by
  unfold codeSum
  rw [← Fin.sum_univ_eq_sum_range]
  simp [FinitePointCloud.paddedCode, FinitePointCloud.toMultiset, FinitePointCloud.toList,
    FinitePointCloud.point?, List.sum_ofFn]
  rfl

/-- Summing any measurable point observable over a finite multiset is measurable. -/
@[fun_prop]
theorem measurable_sum_map {f : X → Y} (hf : Measurable f) :
    Measurable (fun m : Multiset X ↦ (m.map f).sum) := by
  have h := (measurable_codeSum hf).comp
    (FinitePointCloud.measurable_paddedCode.comp measurable_toFinitePointCloud)
  simpa only [Function.comp_def, codeSum_paddedCode_cloud, toMultiset_toFinitePointCloud] using h

omit [StandardBorelSpace X] [MeasurableAdd₂ Y] in
private theorem measurable_option_elim_param {A : Type*} [MeasurableSpace A]
    {f : A × X → Y} (hf : Measurable f) :
    Measurable (fun p : A × Option X ↦ p.2.elim 0 (fun x ↦ f (p.1, x))) := by
  have hc : Measurable (fun p : A × Option X ↦
      (p.1, p.2.elim' (Sum.inl ()) Sum.inr)) :=
    measurable_fst.prodMk ((comap_measurable _).comp measurable_snd)
  have hd := (MeasurableEquiv.prodSumDistrib A Unit X).measurable.comp hc
  have h : Measurable (Sum.elim (fun _ : A × Unit ↦ (0 : Y)) f) :=
    measurable_fun_sum measurable_const hf
  convert h.comp hd using 1
  funext p
  rcases p with ⟨a, o⟩
  cases o <;> rfl

/-- A jointly measurable observable can be summed over a varying finite multiset while keeping
its external parameter. -/
@[fun_prop]
theorem measurable_sum_map_param {A : Type*} [MeasurableSpace A]
    {f : A × X → Y} (hf : Measurable f) :
    Measurable (fun p : A × Multiset X ↦ (p.2.map (fun x ↦ f (p.1, x))).sum) := by
  have hsum : Measurable (fun p : (A × FinitePointCloud.PaddedCode X) × ℕ ↦
      ∑ k ∈ Finset.range p.2, (p.1.2.2 k).elim 0 (fun x ↦ f (p.1.1, x))) := by
    apply measurable_from_prod_countable_left
    intro n
    change Measurable (fun p : A × FinitePointCloud.PaddedCode X ↦
      ∑ k ∈ Finset.range n, (p.2.2 k).elim 0 (fun x ↦ f (p.1, x)))
    apply Finset.measurable_sum
    intro k hk
    exact (measurable_option_elim_param hf).comp
      (measurable_fst.prodMk ((measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)))
  have hcode : Measurable (fun p : A × FinitePointCloud.PaddedCode X ↦
      codeSum (fun x ↦ f (p.1, x)) p.2) :=
    hsum.comp (measurable_id.prodMk (measurable_fst.comp measurable_snd))
  have h := hcode.comp (measurable_fst.prodMk
    ((FinitePointCloud.measurable_paddedCode.comp measurable_toFinitePointCloud).comp measurable_snd))
  simpa only [Function.comp_def, codeSum_paddedCode_cloud, toMultiset_toFinitePointCloud] using h

end Sums

end OTSelector.PointProcess.MultisetEncoding

import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.ProperSpace
import OTSelector.MeasureTheory.FiniteMultisetEncoding
import OTSelector.PointProcess.LocalConfiguration
import OTSelector.PointProcess.LocalConfigurationMultiset

/-!
Conditions: A shell configuration in a metric space and integer window radius; measurable-window statements use the stated standard-Borel point structure and measurable additive targets.

Objects: Finite multiset windows equal to open integer balls with full multiplicities, consistent nested restrictions, and measurable finite window sums/cardinalities.

Proof detail: Sum the finitely many shell multisets below the radius. Unique shell membership computes each count; multiset extensionality gives nested restriction and finite-sum measurability gives observable readouts.

References: Günter Last; Mathew Penrose: Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10; Günter Last; Mathew Penrose: Section 2.4, Definition 2.11 and following integer-ball exhaustion criterion, p. 16.
Relation: Actual bounded-window counting on the shell code. The module proves measurability of hard-window readouts, not continuity across their shell boundaries.
-/


/-!
## Lemma skeleton

* **Conditions:** X is metric and config is a shell configuration at an arbitrary base. N and M are natural integer window radii; the nested-window identity assumes M <= N. The algebraic observable-sum formula works for any additive commutative monoid Y. Measurable window sums additionally require X Borel and standard Borel, Y measurable with measurable addition, and a measurable point observable.
* **Objects:** window config N: finite multiset formed by the first N shell multisets after forgetting shell subtype certificates; count_window: multiplicity restricted by the strict condition dist(x,base)<N; sum_map_window: finite sum of an observable over the integer-ball window
* **Proof detail:** Flatten the finite family of shell multisets indexed by range N. Use the uniqueness of shell membership and shellIndex<N iff dist<N to compute each point count. Apply multiset extensionality to the nested restriction identity. Distribute multiset maps and sums over the finite shell sum; combine the previously proved multiset-sum measurability.

## Mathematical sources

* Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*, Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10.
  https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22
* Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*, Section 2.4, Definition 2.11 and following integer-ball exhaustion criterion, p. 16.
  https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=28
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31.
  https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30

**Relationship to the sources:** Integer open-ball restriction and finite shell sums implement bounded-window counting. Measurability follows from the code; continuity across a hard shell boundary is not asserted.
-/

/-!
# Finite windows of a locally finite configuration

The first `N` shells encode exactly the open ball of integer radius `N` about the base point.
This file proves the equality with multiplicities, consistency of nested windows, and
measurability of finite-window sums and counts.  These are operations on the actual shell code;
no topology or compactness assumption about the configuration space is used.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] {base : X}

/-- All points in the open ball of radius `N`, retaining their multiplicities. -/
noncomputable def window (config : LocalConfiguration base) (N : ℕ) : Multiset X :=
  ∑ n ∈ Finset.range N, (config n).map Subtype.val

/-- A shell contributes exactly the multiplicity of points belonging to that shell. -/
theorem count_shell_map (config : LocalConfiguration base) (n : ℕ) (x : X) :
    ((config n).map Subtype.val).count x =
      if n = shellIndex base x then multiplicity config x else 0 := by
  by_cases hn : n = shellIndex base x
  · subst n
    simpa only [multiplicity, ↓reduceIte] using
      Multiset.count_map_eq_count'
        (Subtype.val : Shell base (shellIndex base x) → X)
        (config (shellIndex base x)) Subtype.val_injective ⟨x, rfl⟩
  · simp only [hn, ↓reduceIte]
    apply Multiset.count_eq_zero_of_notMem
    rintro hx
    obtain ⟨y, hy, hyx⟩ := Multiset.mem_map.mp hx
    exact hn (y.property.symm.trans (congrArg (shellIndex base) hyx))

/-- The multiplicity in an integer-radius window is exactly the original multiplicity inside
the ball, and zero outside. -/
theorem count_window (config : LocalConfiguration base) (N : ℕ) (x : X) :
    (window config N).count x =
      if dist x base < (N : ℝ) then multiplicity config x else 0 := by
  change (Multiset.countAddMonoidHom x) (∑ n ∈ Finset.range N, (config n).map Subtype.val) = _
  rw [map_sum]
  simp only [Multiset.coe_countAddMonoidHom, count_shell_map]
  simp [Finset.sum_ite_eq', shellIndex_lt_iff]

/-- Membership in a window is the geometric ball condition and positive point multiplicity. -/
theorem mem_window_iff (config : LocalConfiguration base) (N : ℕ) (x : X) :
    x ∈ window config N ↔ dist x base < (N : ℝ) ∧ multiplicity config x ≠ 0 := by
  rw [← Multiset.count_ne_zero, count_window]
  split_ifs <;> simp_all

/-- Restricting a larger window to a smaller integer-radius ball recovers the smaller window. -/
theorem filter_window (config : LocalConfiguration base) {M N : ℕ} (hMN : M ≤ N) :
    (window config N).filter (fun x ↦ dist x base < (M : ℝ)) = window config M := by
  apply Multiset.ext.mpr
  intro x
  by_cases hx : dist x base < (M : ℝ)
  · have hxN : dist x base < (N : ℝ) := hx.trans_le (by exact_mod_cast hMN)
    simp [hx, hxN, count_window]
  · simp [hx, count_window]

/-- A finite-window sum decomposes into the finitely many constituent shell sums. -/
theorem sum_map_window {Y : Type*} [AddCommMonoid Y]
    (config : LocalConfiguration base) (N : ℕ) (f : X → Y) :
    ((window config N).map f).sum =
      ∑ n ∈ Finset.range N, ((config n).map (fun x ↦ f x.val)).sum := by
  induction N with
  | zero => simp [window]
  | succ N hN =>
      simp only [window, Finset.sum_range_succ] at hN ⊢
      rw [Multiset.map_add, Multiset.sum_add, hN, Multiset.map_map]
      rfl

/-- The total point count of a window is the sum of its shell counts. -/
theorem card_window (config : LocalConfiguration base) (N : ℕ) :
    (window config N).card = ∑ n ∈ Finset.range N, (config n).card := by
  simp [window, Multiset.card_sum]

section Measurable

variable [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]

/-- Finite-window sums of a measurable point observable are measurable. -/
@[fun_prop]
theorem measurable_sum_map_window {Y : Type*} [AddCommMonoid Y]
    [MeasurableSpace Y] [MeasurableAdd₂ Y] {f : X → Y} (hf : Measurable f) (N : ℕ) :
    Measurable (fun config : LocalConfiguration base ↦ ((window config N).map f).sum) := by
  simp_rw [sum_map_window]
  apply Finset.measurable_sum
  intro n hn
  exact (MultisetEncoding.measurable_sum_map (hf.comp measurable_subtype_coe)).comp
    (measurable_shell n)

/-- Window counts, with multiplicity, are measurable. -/
@[fun_prop]
theorem measurable_card_window (N : ℕ) :
    Measurable (fun config : LocalConfiguration base ↦ (window config N).card) := by
  simp_rw [card_window]
  exact Finset.measurable_sum _ fun n hn ↦ measurable_shell_card n

end Measurable

end OTSelector.PointProcess.LocalConfiguration

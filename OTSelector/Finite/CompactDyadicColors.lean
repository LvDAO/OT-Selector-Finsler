import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.DyadicCube

/-!
# Finite.CompactDyadicColors

**Conditions:** Finitely many compact source/target color sets in a dyadic unit cube are disjoint across different colors.

**Objects:** One common dyadic level separating all compact cross colors.

**Proof detail:** Compact disjoint pairs have positive distance; choose a dyadic diameter below each separation and take the maximum of the finitely many levels, so an equal cell forces equal colors.

**Sources:** [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110), Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products); [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/html/sec_metcont.html), Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! A sufficiently fine original dyadic cell cannot meet two disjoint compact
colors. This separates finitely many retained coordinate images without a
Lipschitz bound on the change between their original coordinate systems. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction

/-- Equal actual closed-cube cells control the original cube metric,
including points on any face or at coordinate one. -/
theorem dist_le_of_dyadicCubeCell_eq {q k : ℕ} {x y : DyadicUnitCube q}
    (hcell : dyadicCubeCell k x = dyadicCubeCell k y) :
    dist x y ≤ ((2 : ℝ) ^ k)⁻¹ := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have h := (norm_le_pi_norm (dyadicCubePoint x - dyadicCubePoint y) i).trans
    (dyadicCube_dist_le_of_cell_eq k x y hcell)
  simpa only [Subtype.dist_eq, Real.dist_eq, Pi.sub_apply, dyadicCubePoint,
    Real.norm_eq_abs] using h

/-- All sufficiently fine actual dyadic cells separate distinct cross-color
compact images. Images of the same color may overlap. -/
theorem exists_dyadic_level_separating_compact_cross_colors
    {I : Type*} [Fintype I] (q : ℕ) (KS KT : I → Set (DyadicUnitCube q))
    (hcompactS : ∀ i, IsCompact (KS i)) (hcompactT : ∀ j, IsCompact (KT j))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (KS i) (KT j)) :
    ∃ level : ℕ, ∀ k ≥ level, ∀ i j, ∀ x ∈ KS i, ∀ y ∈ KT j,
      dyadicCubeCell k x = dyadicCubeCell k y → i = j := by
  have hsmall : Tendsto (fun k : ℕ ↦ ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (2 : ℝ)⁻¹ by positivity) (by norm_num)
  have hpair (i j : I) : ∀ᶠ k : ℕ in atTop,
      ∀ x ∈ KS i, ∀ y ∈ KT j, dyadicCubeCell k x = dyadicCubeCell k y → i = j := by
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ _ _ _ _ _ ↦ hij
    obtain ⟨gap, hgap, hseparate⟩ :=
      Metric.exists_pos_forall_lt_edist (hcompactS i) (hcompactT j).isClosed (hdisjoint i j hij)
    have hgapreal : (0 : ℝ) < gap := by exact_mod_cast hgap
    filter_upwards [hsmall.eventually (Iio_mem_nhds hgapreal)] with k hk x hx y hy hcell
    have hdist : dist x y ≤ ((2 : ℝ) ^ k)⁻¹ :=
      dist_le_of_dyadicCubeCell_eq hcell
    have hsep : (gap : ℝ) < dist x y := by
      have hnn : gap < nndist x y :=
        ENNReal.coe_lt_coe.mp (by simpa only [edist_nndist] using hseparate x hx y hy)
      exact_mod_cast hnn
    exact False.elim (lt_asymm hsep (hdist.trans_lt hk))
  have hall : ∀ᶠ k : ℕ in atTop, ∀ i j, ∀ x ∈ KS i, ∀ y ∈ KT j,
      dyadicCubeCell k x = dyadicCubeCell k y → i = j :=
    eventually_all.mpr fun i ↦ eventually_all.mpr fun j ↦ hpair i j
  exact eventually_atTop.mp hall

/-- The common compact-color version, obtained without strengthening the
cross-color separation needed by the original hierarchy. -/
theorem exists_dyadic_level_separating_compact_colors
    {I : Type*} [Fintype I] (q : ℕ) (K : I → Set (DyadicUnitCube q))
    (hcompact : ∀ i, IsCompact (K i)) (hdisjoint : Pairwise (Disjoint on K)) :
    ∃ level : ℕ, ∀ k ≥ level, ∀ i j, ∀ x ∈ K i, ∀ y ∈ K j,
      dyadicCubeCell k x = dyadicCubeCell k y → i = j :=
  exists_dyadic_level_separating_compact_cross_colors q K K hcompact hcompact
    (fun _ _ hij ↦ hdisjoint hij)

/-- One depth works for every original type. Compact coordinate images from
different types may overlap because the original hierarchy keeps their tags. -/
theorem exists_dyadic_level_separating_typed_compact_colors
    {T I : Type*} [Fintype T] [Fintype I] (q : ℕ)
    (K : T → I → Set (DyadicUnitCube q))
    (hcompact : ∀ t i, IsCompact (K t i))
    (hdisjoint : ∀ t, Pairwise (Disjoint on K t)) :
    ∃ level : ℕ, ∀ k ≥ level, ∀ t i j, ∀ x ∈ K t i, ∀ y ∈ K t j,
      dyadicCubeCell k x = dyadicCubeCell k y → i = j := by
  classical
  choose level hlevel using fun t ↦
    exists_dyadic_level_separating_compact_colors q (K t) (hcompact t) (hdisjoint t)
  refine ⟨Finset.univ.sup level, fun k hk t i j x hx y hy hcell ↦ ?_⟩
  exact hlevel t k ((Finset.le_sup (Finset.mem_univ t)).trans hk) i j x hx y hy hcell

end OTSelector.Reconstruction

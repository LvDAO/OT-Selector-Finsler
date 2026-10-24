import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Calculus.Whitney.C1
import OTSelector.MeasureTheory.LusinCompactCore

/-!
# Compact differential jets and a Lusin Whitney extension

Main declarations: exists_whitney_compact_jet_of_lipschitzOn; exists_contDiff_one_lusin_extension_of_lipschitzOn.

This file contains the original declarations and their proofs. The source-unit
sections below preserve each unit's conditions, objects, proof details and
book or paper locations.
-/

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.DifferentialLusinCore`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional real normed domain/target and Borel measure structure; finite measured set and almost-everywhere full differentiability. Lipschitz variants use Haar measure or an absolutely continuous measure, and openness for local Lipschitz data.
* **Objects:** A compact set with arbitrarily small discarded mass, consisting of actual differentiability points where the original map and actual derivative are continuous.
* **Proof detail:** Use measurability of the differentiability set and actual derivative, restrict to the full differentiability set and apply compact Lusin. Rademacher and absolute continuity supply the a.e. premise in Lipschitz variants.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Section 262P, p. 17 (measurability of derivative); Theorem 262Q, pp. 18–20 (Rademacher).
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=17
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416.
  https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110

**Relationship to the sources:** An application of derivative measurability, Rademacher and Lusin; it does not yet assert uniform Whitney remainder or an extension.
-/

/-!
# Compact cores for the actual first derivative

A function that is differentiable almost everywhere on a finite-measure set admits
large compact subsets consisting entirely of differentiability points, on which its
actual derivative is continuous. Rademacher's theorem supplies the hypothesis for
Lipschitz functions and measures absolutely continuous with respect to Haar measure.
-/

open Set MeasureTheory Filter
open scoped ENNReal NNReal

namespace OTSelector.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Almost-everywhere differentiability on a finite-measure set gives a large compact
core of actual differentiability points on which the original map and its actual
Fréchet derivative are both continuous. -/
theorem exists_differential_lusin_compact_core
    {μ : Measure E} {s : Set E} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    {f : E → F} (hdiff : ∀ᵐ x ∂(μ.restrict s), DifferentiableAt ℝ f x)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ μ (s \ K) < ε ∧
      (∀ x ∈ K, DifferentiableAt ℝ f x) ∧
      ContinuousOn f K ∧ ContinuousOn (fderiv ℝ f) K := by
  let D : Set E := {x | DifferentiableAt ℝ f x}
  have hD : MeasurableSet D := measurableSet_of_differentiableAt ℝ f
  have hnull : μ (s \ D) = 0 := by
    change μ {x | x ∈ s ∧ ¬DifferentiableAt ℝ f x} = 0
    simpa only [not_imp] using ae_iff.mp ((ae_restrict_iff' hs).mp hdiff)
  obtain ⟨K, hKsub, hK, hsmall, hdK⟩ := exists_lusin_compact_core (hs.inter hD)
    (ne_top_of_le_ne_top hμs (measure_mono inter_subset_left)) (measurable_fderiv ℝ f) hε
  have hactual (x : E) (hx : x ∈ K) : DifferentiableAt ℝ f x := (hKsub hx).2
  refine ⟨K, hKsub.trans inter_subset_left, hK, ?_, hactual,
    fun x hx ↦ (hactual x hx).continuousAt.continuousWithinAt, hdK⟩
  calc
    μ (s \ K) ≤ μ ((s ∩ D) \ K ∪ (s \ D)) := measure_mono (by
      intro x hx
      by_cases hxD : x ∈ D
      · exact Or.inl ⟨⟨hx.1, hxD⟩, hx.2⟩
      · exact Or.inr ⟨hx.1, hxD⟩)
    _ ≤ μ ((s ∩ D) \ K) + μ (s \ D) := measure_union_le _ _
    _ = μ ((s ∩ D) \ K) := by rw [hnull, add_zero]
    _ < ε := hsmall

/-- Rademacher's theorem and the compact-core construction apply directly to an original
Lipschitz map between finite-dimensional real normed spaces, with Haar measure. -/
theorem exists_differential_lusin_compact_core_of_lipschitz
    {μ : Measure E} [μ.IsAddHaarMeasure] {s : Set E}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ μ (s \ K) < ε ∧
      (∀ x ∈ K, DifferentiableAt ℝ f x) ∧
      ContinuousOn f K ∧ ContinuousOn (fderiv ℝ f) K := by
  apply exists_differential_lusin_compact_core hs hμs _ hε
  exact ae_restrict_of_ae hf.ae_differentiableAt

/-- The discarded mass can be measured by any measure absolutely continuous with respect
to Haar measure, in particular the original measure with a density on a coordinate chart. -/
theorem exists_differential_lusin_compact_core_of_lipschitz_absolutelyContinuous
    {μ ν : Measure E} [μ.IsAddHaarMeasure] (hν : ν ≪ μ) {s : Set E}
    (hs : MeasurableSet s) (hνs : ν s ≠ ∞)
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ ν (s \ K) < ε ∧
      (∀ x ∈ K, DifferentiableAt ℝ f x) ∧
      ContinuousOn f K ∧ ContinuousOn (fderiv ℝ f) K := by
  apply exists_differential_lusin_compact_core hs hνs _ hε
  exact ae_restrict_of_ae (hν.ae_le hf.ae_differentiableAt)

/-- A Lipschitz restriction to an open coordinate neighborhood suffices. The selected core
consists of full differentiability points of the original map, not merely derivatives within
an arbitrary assigned label set. -/
theorem exists_differential_lusin_compact_core_of_lipschitzOn
    {μ ν : Measure E} [μ.IsAddHaarMeasure] (hν : ν ≪ μ) {s U : Set E}
    (hs : MeasurableSet s) (hνs : ν s ≠ ∞) (hU : IsOpen U) (hsU : s ⊆ U)
    {f : E → F} {C : ℝ≥0} (hf : LipschitzOnWith C f U)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ ν (s \ K) < ε ∧
      (∀ x ∈ K, DifferentiableAt ℝ f x) ∧
      ContinuousOn f K ∧ ContinuousOn (fderiv ℝ f) K := by
  apply exists_differential_lusin_compact_core hs hνs _ hε
  apply (ae_restrict_iff' hs).mpr
  filter_upwards [hν.ae_le hf.ae_differentiableWithinAt_of_mem] with x hx hxs
  exact (hx (hsU hxs)).differentiableAt (hU.mem_nhds (hsU hxs))

end OTSelector.Geometry

end

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.CompactJet`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional Borel real normed domain, finite measured set and actual differentiability. The compact-subcore helper needs only a normed target; the full a.e./Lipschitz variants have finite-dimensional target.
* **Objects:** Large compact restrictions carrying the original continuous first jet and a uniform first-order Whitney remainder condition.
* **Proof detail:** For every tolerance, measurably choose a discrete differentiability radius. Apply Lusin to the countable product of radius indices; compactness bounds each coordinate, giving a uniform radius. Combine with the differential Lusin core.

## Mathematical sources

* Hassler Whitney, *On totally differentiable and smooth functions, Pacific Journal of Mathematics 1(1), 143–159 (1951)*, Section 2, Theorem 1 and proof, pp. 144–147, especially uniform first-order compatibility (2.8).
  https://msp.org/pjm/1951/1-1/pjm-v1-n1-p15-s.pdf#page=3
* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416.
  https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 262P, p. 17 (measurability of derivative); Theorem 262Q, pp. 18–20 (Rademacher).
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=17

**Relationship to the sources:** A full first-order compatibility preparation for the constructed C1 extension. It follows the uniformization idea in Whitney’s 1951 proof using a countable Lusin-index argument; no density-one-only remainder is substituted for the displayed pairwise compact-set condition.
-/

/-!
# Uniform first-order Whitney bounds on large compact subsets

The radius of the differentiability estimate is selected measurably at each point.
A second Lusin restriction makes all countably many selected radius indices continuous;
compactness then bounds each index uniformly. This supplies the first-order Whitney
condition for the original function and its actual derivative.
-/

open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology

namespace OTSelector.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] in
private theorem isClosed_uniform_first_order_set
    {f : E → F} {D : E → E →L[ℝ] F} {H : Set E} (hH : IsClosed H)
    (hf : ContinuousOn f H) (hD : ContinuousOn D H) (η δ : ℝ) :
    IsClosed (H ∩ {x | ∀ y ∈ H, dist y x < δ →
      ‖f y - f x - D x (y - x)‖ ≤ η * ‖y - x‖}) := by
  apply hH.inter_preimage_val_iff.mp
  have hf' : Continuous (fun x : H ↦ f x) := continuousOn_iff_continuous_domRestrict.mp hf
  have hD' : Continuous (fun x : H ↦ D x) := continuousOn_iff_continuous_domRestrict.mp hD
  change IsClosed {x : H | ∀ y ∈ H, dist y x < δ →
    ‖f y - f x - D x (y - x)‖ ≤ η * ‖y - x‖}
  have hi : IsClosed (⋂ y : H, {x : H | dist (y : E) x < δ →
      ‖f y - f x - D x (y - x)‖ ≤ η * ‖(y : E) - x‖}) := by
    apply isClosed_iInter
    intro y
    have hleft : IsClosed {x : H | δ ≤ dist (y : E) x} :=
      isClosed_le continuous_const (continuous_const.dist continuous_subtype_val)
    have hright : IsClosed {x : H |
        ‖f y - f x - D x (y - x)‖ ≤ η * ‖(y : E) - x‖} :=
      isClosed_le ((continuous_const.sub hf').sub
        (hD'.clm_apply (continuous_const.sub continuous_subtype_val))).norm
        (continuous_const.mul (continuous_const.sub continuous_subtype_val).norm)
    convert hleft.union hright using 1
    ext x
    simp only [mem_union, mem_ofPred_eq, not_lt, imp_iff_not_or]
  convert hi using 1
  ext x
  simp only [mem_ofPred_eq, mem_iInter, Subtype.forall]

omit [FiniteDimensional ℝ F] in
/-- Inside a compact set of actual differentiability points with continuous first jets,
one can retain arbitrarily large compact mass and make all first-order remainder
estimates uniform. No modulus of differentiability is assumed as an input. -/
theorem exists_whitney_compact_subcore
    {μ : Measure E} {H : Set E} (hH : IsCompact H) (hμH : μ H ≠ ∞)
    {f : E → F} (hf : ContinuousOn f H) (hD : ContinuousOn (fderiv ℝ f) H)
    (hdiff : ∀ x ∈ H, DifferentiableAt ℝ f x) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ H, IsCompact K ∧ μ (H \ K) < ε ∧
      ∀ η > 0, ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
        ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ η * ‖y - x‖ := by
  classical
  let a : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  let R : ℕ → ℕ → Set E := fun n m ↦ H ∩ {x | ∀ y ∈ H, dist y x < a m →
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ a n * ‖y - x‖}
  have hR (n m : ℕ) : IsClosed (R n m) :=
    isClosed_uniform_first_order_set hH.isClosed hf hD _ _
  have hex (n : ℕ) (x : E) : ∃ m, x ∉ H ∨ x ∈ R n m := by
    by_cases hx : x ∈ H
    · obtain ⟨r, hr, hbound⟩ := Metric.mem_nhds_iff.mp
        ((hdiff x hx).hasFDerivAt.isLittleO.def (ha n))
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
      refine ⟨m, Or.inr ⟨hx, ?_⟩⟩
      intro y hy hdist
      exact hbound (lt_trans hdist hm)
    · exact ⟨0, Or.inl hx⟩
  let index : E → ℕ → ℕ := fun x n ↦ Nat.find (hex n x)
  have hindex : Measurable index := by
    apply measurable_pi_lambda
    intro n
    exact measurable_find (hex n) (fun m ↦ hH.isClosed.measurableSet.compl.union
      (hR n m).measurableSet)
  obtain ⟨K, hKH, hK, hsmall, hcont⟩ := exists_lusin_compact_core hH.measurableSet
    hμH hindex hε
  refine ⟨K, hKH, hK, hsmall, ?_⟩
  intro η hη
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  have hc : ContinuousOn (fun x ↦ index x n) K :=
    (continuous_apply n).comp_continuousOn hcont
  obtain ⟨N, hN⟩ := hK.bddAbove_image hc
  refine ⟨a N, ha N, ?_⟩
  intro x hx y hy hxy
  have hxR : x ∈ R n (index x n) := (Nat.find_spec (hex n x)).resolve_left (not_not.mpr (hKH hx))
  have hNx : index x n ≤ N := hN (mem_image_of_mem _ hx)
  have hrad : a N ≤ a (index x n) := by
    dsimp [a]
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hNx 1
  have hrem := hxR.2 y (hKH hy) ((dist_comm x y ▸ hxy).trans_le hrad)
  exact hrem.trans (mul_le_mul_of_nonneg_right hn.le (norm_nonneg _))

/-- Almost-everywhere differentiability yields a large compact set carrying the original
continuous first jet and the uniform first-order Whitney remainder condition. -/
theorem exists_whitney_compact_jet
    {μ : Measure E} {s : Set E} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    {f : E → F} (hdiff : ∀ᵐ x ∂(μ.restrict s), DifferentiableAt ℝ f x)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ μ (s \ K) < ε ∧
      (∀ x ∈ K, DifferentiableAt ℝ f x) ∧
      ContinuousOn f K ∧ ContinuousOn (fderiv ℝ f) K ∧
      ∀ η > 0, ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
        ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ η * ‖y - x‖ := by
  obtain ⟨H, hHs, hH, hsmallH, hdiffH, hfH, hDH⟩ :=
    exists_differential_lusin_compact_core hs hμs hdiff (ENNReal.half_pos hε).ne'
  obtain ⟨K, hKH, hK, hsmallK, hrem⟩ := exists_whitney_compact_subcore hH
    (ne_top_of_le_ne_top hμs (measure_mono hHs)) hfH hDH hdiffH (ENNReal.half_pos hε).ne'
  refine ⟨K, hKH.trans hHs, hK, ?_, fun x hx ↦ hdiffH x (hKH hx),
    hfH.mono hKH, hDH.mono hKH, hrem⟩
  calc
    μ (s \ K) ≤ μ (s \ H ∪ (H \ K)) := measure_mono (by
      intro x hx
      by_cases hxH : x ∈ H
      · exact Or.inr ⟨hxH, hx.2⟩
      · exact Or.inl ⟨hx.1, hxH⟩)
    _ ≤ μ (s \ H) + μ (H \ K) := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hsmallH hsmallK
    _ = ε := ENNReal.add_halves ε

/-- For a locally represented Lipschitz map, the full Whitney condition holds on a large
compact part of the assigned measurable set, with loss measured by any measure absolutely
continuous with respect to Haar measure. -/
theorem exists_whitney_compact_jet_of_lipschitzOn
    {μ ν : Measure E} [μ.IsAddHaarMeasure] (hν : ν ≪ μ) {s U : Set E}
    (hs : MeasurableSet s) (hνs : ν s ≠ ∞) (hU : IsOpen U) (hsU : s ⊆ U)
    {f : E → F} {C : ℝ≥0} (hf : LipschitzOnWith C f U)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ ν (s \ K) < ε ∧
      (∀ x ∈ K, DifferentiableAt ℝ f x) ∧
      ContinuousOn f K ∧ ContinuousOn (fderiv ℝ f) K ∧
      ∀ η > 0, ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
        ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ η * ‖y - x‖ := by
  apply exists_whitney_compact_jet hs hνs _ hε
  apply (ae_restrict_iff' hs).mpr
  filter_upwards [hν.ae_le hf.ae_differentiableWithinAt_of_mem] with x hx hxs
  exact (hx (hsU hxs)).differentiableAt (hU.mem_nhds (hsU hxs))

/-- A globally Lipschitz map has compact Whitney cores with arbitrarily small loss of any
original measure absolutely continuous with respect to Haar measure. -/
theorem exists_whitney_compact_jet_of_lipschitz
    {μ ν : Measure E} [μ.IsAddHaarMeasure] (hν : ν ≪ μ) {s : Set E}
    (hs : MeasurableSet s) (hνs : ν s ≠ ∞)
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ ν (s \ K) < ε ∧
      (∀ x ∈ K, DifferentiableAt ℝ f x) ∧
      ContinuousOn f K ∧ ContinuousOn (fderiv ℝ f) K ∧
      ∀ η > 0, ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
        ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ η * ‖y - x‖ := by
  exact exists_whitney_compact_jet_of_lipschitzOn hν hs hνs isOpen_univ
    (subset_univ s) hf.lipschitzOnWith hε

end OTSelector.Geometry

end

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.LusinExtension`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional Borel real normed domain/target, original measure absolutely continuous with respect to Haar measure, finite measured subset of an open domain and a Lipschitz map on that domain.
* **Objects:** A large compact set and a genuine global C1 map matching both the original values and actual first derivatives everywhere on that set.
* **Proof detail:** Construct the large compact Whitney first jet using Rademacher and Lusin, then apply the actually proved compact C1 extension. Derivative equality follows from the prescribed derivative property.

## Mathematical sources

* Hassler Whitney, *On totally differentiable and smooth functions, Pacific Journal of Mathematics 1(1), 143–159 (1951)*, Section 2, Theorem 1 and proof, pp. 144–147, especially uniform first-order compatibility (2.8).
  https://msp.org/pjm/1951/1-1/pjm-v1-n1-p15-s.pdf#page=3
* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Section 4, Theorem I, p. 65; Section 11, Lemma 2 and proof, pp. 69–71, equations (11.1)–(11.8).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=3
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416.
  https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 262P, p. 17 (measurability of derivative); Theorem 262Q, pp. 18–20 (Rademacher).
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=17

**Relationship to the sources:** A measure/coordinate-adapted vector-valued Lusin C1 approximation, analogous to Whitney’s 1951 large-set extension. The statement uses full derivatives on its compact set and does not assert a global Lipschitz bound on the C1 extension.
-/

/-!
# A global C1 extension on a large compact part of a Lipschitz map

For the original measure, absolutely continuous with respect to Haar measure, a
Lipschitz map on an open set agrees with a genuine global C1 map on a compact subset
with arbitrarily small prescribed mass loss. The actual derivatives agree there too.
The compact jet and the extension are constructed, rather than supplied as inputs.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace OTSelector.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A Lipschitz map on an open set has a genuine global C1 representative on a compact
part of any prescribed measurable subset of finite original mass, with arbitrarily
small mass loss. Both its values and its actual derivatives are preserved on that part. -/
theorem exists_contDiff_one_lusin_extension_of_lipschitzOn
    {μ ν : Measure E} [μ.IsAddHaarMeasure] (hν : ν ≪ μ) {s U : Set E}
    (hs : MeasurableSet s) (hνs : ν s ≠ ∞) (hU : IsOpen U) (hsU : s ⊆ U)
    {f : E → F} {C : ℝ≥0} (hf : LipschitzOnWith C f U)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ ν (s \ K) < ε ∧
      (∀ x ∈ K, DifferentiableAt ℝ f x) ∧
      ∃ G : E → F, ContDiff ℝ 1 G ∧ EqOn G f K ∧
        EqOn (fderiv ℝ G) (fderiv ℝ f) K := by
  obtain ⟨K, hKs, hK, hsmall, hdiff, _, hD, hrem⟩ :=
    exists_whitney_compact_jet_of_lipschitzOn hν hs hνs hU hsU hf hε
  have hWhitney : ∀ η > 0, ∃ δ > 0, ∀ u ∈ K, ∀ v ∈ K, dist u v < δ →
      ‖f u - f v - fderiv ℝ f v (u - v)‖ ≤ η * ‖u - v‖ := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hrem η hη
    refine ⟨δ, hδ, fun u hu v hv huv ↦ ?_⟩
    exact hbound v hv u hu (by simpa only [dist_comm] using huv)
  obtain ⟨G, hG, hval, hderiv⟩ := exists_contDiff_one_extension_of_whitney hK hD hWhitney
  exact ⟨K, hKs, hK, hsmall, hdiff, G, hG, hval, fun x hx ↦ (hderiv x hx).fderiv⟩

end OTSelector.Geometry

end

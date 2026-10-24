import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import OTSelector.Analysis.Calculus.Whitney.Basic
import OTSelector.Analysis.Calculus.Whitney.Proofs.Boundary
import OTSelector.Analysis.Calculus.Whitney.Proofs.Cover
import OTSelector.Analysis.Calculus.Whitney.Proofs.Partition

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional real normed domain, arbitrary real normed target, compact K, continuous prescribed linear-map field D and uniform first-order Whitney remainder.
* **Objects:** A genuine global C1 map equal to f on K, with actual derivative D at every point of K.
* **Proof detail:** Construct the cover, normalized smooth weights and nearest anchors. Set the extension equal to f on K and to the actual locally finite affine interpolation off K, then prove its boundary derivative and derivative continuity.

## Mathematical sources

* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2
* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Sections 7–10, pp. 67–69: smooth localization, complement decomposition, normalized weights (9.2), derivative scaling (10.1).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=5
* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Section 4, Theorem I, p. 65; Section 11, Lemma 2 and proof, pp. 69–71, equations (11.1)–(11.8).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=3

**Relationship to the sources:** A compact, first-order, vector-valued specialization of the genuine Whitney extension construction, without claiming arbitrary-order or real-analytic extension. An extension, cover and partition are all constructed.
-/

/-!
# A constructed C1 extension of a compact Whitney first jet

The extension is the prescribed function on the compact set and the actual locally
finite normalized affine interpolation on its complement. The cover, smooth weights,
derivative mass bound, nearest anchors, boundary differentiability and continuity of
the actual derivative are all constructed. No extension or partition oracle is an input.
-/

open Set Filter Metric Function
open scoped Topology ContDiff BigOperators

noncomputable section
namespace OTSelector.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous derivative field with a uniform first-order Whitney remainder on a
compact set extends to a genuine global C1 map, matching both values and derivatives. -/
theorem exists_contDiff_one_extension_of_whitney {K : Set E} (hK : IsCompact K)
    {f : E → F} {D : E → E →L[ℝ] F} (hD : ContinuousOn D K)
    (hWhitney : ∀ ε > 0, ∃ δ > 0, ∀ u ∈ K, ∀ v ∈ K, dist u v < δ →
      ‖f u - f v - D v (u - v)‖ ≤ ε * ‖u - v‖) :
    ∃ G : E → F, ContDiff ℝ 1 G ∧ EqOn G f K ∧
      ∀ b ∈ K, HasFDerivAt G (D b) b := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨C, ψ, A, hA, hC, hsupp, hLF, hprops⟩ :=
      exists_whitney_partition hK.isClosed hne
    choose a ha hdist using fun c : C ↦ hK.exists_infDist_eq_dist hne (c : E)
    let G : E → F := fun x ↦ if x ∈ K then f x else
      ∑ᶠ c : C, ψ c x • whitneyAffineJet f D (a c) x
    have hGK : EqOn G f K := by intro x hx; simp [G, hx]
    have hlocal (x : E) (hx : x ∉ K) : HasWhitneyLocalBlend K ψ f D a G (16 * A) x := by
      obtain ⟨s, hs, hout⟩ := exists_whitney_support_finset hK.isClosed hLF hx
      have hz : ∀ᶠ y in 𝓝 x, ∀ c ∉ s, ψ c y = 0 := by
        filter_upwards [hout] with y hy c hc
        apply notMem_support.mp
        exact fun h ↦ hy c hc (hsupp c (subset_tsupport _ h))
      have hzero (c : C) (hc : c ∉ s) : ψ c =ᶠ[𝓝 x] fun _ ↦ 0 := by
        filter_upwards [hz] with y hy
        exact hy c hc
      have hgerm : G =ᶠ[𝓝 x] whitneyBlend s ψ f D a := by
        filter_upwards [hz, hK.isClosed.isOpen_compl.mem_nhds hx] with y hy hyK
        dsimp only [G, whitneyBlend]
        simp only [show ¬ y ∈ K from hyK, ↓reduceIte]
        apply finsum_eq_sum_of_support_subset
        intro c hc
        by_contra hcs
        exact hc (by
          change ψ c y • whitneyAffineJet f D (a c) y = 0
          rw [hy c hcs, zero_smul])
      have hone : (fun y ↦ ∑ c ∈ s, ψ c y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := by
        filter_upwards [hz, hK.isClosed.isOpen_compl.mem_nhds hx] with y hy hyK
        have heq : (∑ᶠ c, ψ c y) = ∑ c ∈ s, ψ c y := by
          apply finsum_eq_sum_of_support_subset
          intro c hc
          by_contra hcs
          exact hc (hy c hcs)
        rw [← heq]
        exact (hprops y hyK).2.2.1
      refine ⟨s, hgerm, fun c _ ↦ ((hprops x hx).2.2.2.1 c).of_le (by simp),
        fun c _ ↦ (hprops x hx).1 c, hone, ?_, ?_⟩
      · intro c hc
        refine ⟨ha c, ?_⟩
        have hd := mem_closedBall.mp (hs c hc)
        have hr : whitneyCoverRadius K c ≤ infDist (c : E) K / 16 := min_le_right _ _
        have hl := (infDist_comparable_on_whitneyCoverRadius_ball (hs c hc)).1
        have ht := dist_triangle x (c : E) (a c)
        rw [← hdist c] at ht
        rw [← dist_eq_norm]
        have hn := infDist_nonneg (x := (c : E)) (s := K)
        linarith
      · intro hsmall
        have hnorm : support (fun c ↦ ‖fderiv ℝ (ψ c) x‖) ⊆ (s : Set C) := by
          intro c hc
          by_contra hcs
          have hd := (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).congr_of_eventuallyEq
            (hzero c hcs)
          exact hc (by
            change ‖fderiv ℝ (ψ c) x‖ = 0
            rw [hd.fderiv, norm_zero])
        rw [← finsum_eq_sum_of_support_subset _ hnorm]
        have hh := (hprops x hx).2.2.2.2.2
        have hr : whitneyCoverRadius K x = infDist x K / 16 :=
          min_eq_right (by linarith)
        rw [hr] at hh
        convert hh using 1
        ring
    obtain ⟨hG, hDG⟩ := contDiff_whitney_of_local_blends hK (by positivity) hD hWhitney hGK hlocal
    exact ⟨G, hG, hGK, hDG⟩
  · have hKempty : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ ↦ 0, contDiff_const, ?_, ?_⟩ <;> simp [hKempty]

end OTSelector.Geometry


import LeanLevy.RandomMeasure.PoissonRandomMeasure
import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import LeanPool.Vlasov.OT.Coupling
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.HausdorffDimension
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MarkedStationaryValueLegalClockCollars.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MarkedStationaryValueLegalClockCollars`; the selected original proof blocks follow. -/
section

/-!
# Transport.CompactClockCoercivity

* **Conditions:** Finite clock populations are carried on a measurable legal set; separated compact color carriers and a continuous positive-definite matrix represent the coefficient on legal ordered pairs.
* **Objects:** Large compact legal clock collars and a collar-dependent positive quadratic coercivity constant.
* **Proof detail:** Use inner regularity to remove arbitrarily small endpoint mass, retain compact separated pairs, and minimize the positive quadratic form over that compact set times the unit sphere.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=3): Definition 411B, pp. 3–4, and Lemma 412A(c), pp. 10–11.
- [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660): Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root).
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): The compact positive-matrix argument is classical; the collar-specific constant is derived and imposes no uniform positivity at excluded endpoints.
-/

/-!
# Compact interior collars for the original, possibly degenerate coefficient

Null endpoint mass is removed in the original two clock populations. Each
retained compact collar has its own positive coercivity constant, obtained
from the actual continuous positive coefficient. No common lower bound at
the discarded focal endpoints is required.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Inner regularity approximates an original full-mass clock domain from
inside; the removed mass is measured in that same original law. -/
theorem exists_compact_subset_full_clock_compl_lt
    (μ : Measure ℝ) [IsFiniteMeasure μ] {J : Set ℝ}
    (hJ : MeasurableSet J) (hfull : μ Jᶜ = 0)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : Set ℝ, A ⊆ J ∧ IsCompact A ∧ μ Aᶜ < ε := by
  obtain ⟨A, hAJ, hA, hsmall⟩ :=
    hJ.exists_isCompact_sdiff_lt (measure_ne_top μ J) hε.ne'
  refine ⟨A, hAJ, hA, lt_of_le_of_lt ?_ hsmall⟩
  calc
    μ Aᶜ ≤ μ (Jᶜ ∪ (J \ A)) := measure_mono (by
      intro x hx
      by_cases h : x ∈ J
      · exact Or.inr ⟨h, hx⟩
      · exact Or.inl h)
    _ ≤ μ Jᶜ + μ (J \ A) := measure_union_le _ _
    _ = μ (J \ A) := by rw [hfull, zero_add]

/-- The actual interior coefficient produces arbitrarily full compact clock
collars and an allowed-edge lower bound on each. The original source and
target carriers may interleave; only their absolute separation is used. -/
theorem exists_compact_legal_clock_collars
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {J A₀ B₀ : Set ℝ} (hJ : MeasurableSet J)
    (hA₀ : MeasurableSet A₀) (hB₀ : MeasurableSet B₀)
    (hαJ : α Jᶜ = 0) (hβJ : β Jᶜ = 0)
    (hαA : α A₀ᶜ = 0) (hβB : β B₀ᶜ = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ A₀, ∀ b ∈ B₀, δ ≤ |b - a|)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix {p | p.1 ∈ J ∧ p.2 ∈ J ∧ p.1 < p.2})
    (hpos : ∀ p, p.1 ∈ J → p.2 ∈ J → p.1 < p.2 → (matrix p).PosDef)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hactual : ∀ a ∈ J ∩ A₀, ∀ b ∈ J ∩ B₀, a < b → ∀ v,
      kin a b v = matrixQuadratic (matrix (a, b)) v)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A B : Set ℝ, IsCompact A ∧ IsCompact B ∧
      A ⊆ J ∩ A₀ ∧ B ⊆ J ∩ B₀ ∧ α Aᶜ < ε ∧ β Bᶜ < ε ∧
      ∃ c > 0, ∀ a ∈ A, ∀ b ∈ B, a < b → ∀ v,
        c * ‖v‖ ^ 2 ≤ kin a b v := by
  have hα : α (J ∩ A₀)ᶜ = 0 := by
    apply le_antisymm ?_ bot_le
    exact (measure_mono (by intro x hx; simpa only [mem_compl_iff, mem_inter_iff, mem_union,
      not_and_or] using hx)).trans ((measure_union_le Jᶜ A₀ᶜ).trans_eq (by simp [hαJ, hαA]))
  have hβ : β (J ∩ B₀)ᶜ = 0 := by
    apply le_antisymm ?_ bot_le
    exact (measure_mono (by intro x hx; simpa only [mem_compl_iff, mem_inter_iff, mem_union,
      not_and_or] using hx)).trans ((measure_union_le Jᶜ B₀ᶜ).trans_eq (by simp [hβJ, hβB]))
  obtain ⟨A, hAJ, hA, hαsmall⟩ := exists_compact_subset_full_clock_compl_lt α (hJ.inter hA₀) hα hε
  obtain ⟨B, hBJ, hB, hβsmall⟩ := exists_compact_subset_full_clock_compl_lt β (hJ.inter hB₀) hβ hε
  let K : Set (ℝ × ℝ) := (A ×ˢ B) ∩ {p | δ ≤ p.2 - p.1}
  have hK : IsCompact K := (hA.prod hB).inter_right
    (isClosed_le continuous_const (continuous_snd.sub continuous_fst))
  have hKsub : K ⊆ {p | p.1 ∈ J ∧ p.2 ∈ J ∧ p.1 < p.2} := by
    intro p hp
    exact ⟨(hAJ hp.1.1).1, (hBJ hp.1.2).1, by have := hp.2; dsimp at this; linarith⟩
  obtain ⟨c, hc, hcoercive⟩ := exists_uniform_matrixQuadratic_lower_bound hK
    (hmatrix.mono hKsub) (fun p hp ↦ hpos p (hKsub hp).1 (hKsub hp).2.1 (hKsub hp).2.2)
  refine ⟨A, B, hA, hB, hAJ, hBJ, hαsmall, hβsmall, c, hc, ?_⟩
  intro a ha b hb hab v
  have hgap : δ ≤ b - a := by
    simpa only [abs_of_pos (sub_pos.mpr hab)] using hsep a (hAJ ha).2 b (hBJ hb).2
  rw [hactual a (hAJ ha) b (hBJ hb) hab v]
  exact hcoercive (a, b) ⟨⟨ha, hb⟩, hgap⟩ v

end OTSelector.Reconstruction

end
end

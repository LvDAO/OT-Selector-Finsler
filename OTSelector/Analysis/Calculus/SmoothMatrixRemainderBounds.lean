import LeanLevy.RandomMeasure.PoissonRandomMeasure
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
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
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
import Mathlib.Topology.MetricSpace.HausdorffDimension
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.SmoothPoleRemainderBounds.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.SmoothPoleRemainderBounds`; the selected original proof blocks follow. -/
section

/-!
Conditions: A genuinely smooth matrix-valued remainder on an open interval about zero.

Objects: A smaller compact interval with actual uniform norm and Lipschitz bounds.

Proof detail: Choose a closed subinterval inside the smooth domain and bound the map and its derivative there, then apply the mean-value estimate.

Sources: Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Compact smooth-map estimate; no simple-pole expansion is inferred from the file name.
-/

/-! A genuine smooth endpoint remainder supplies its own compact norm and Lipschitz bounds. -/

open Set Matrix
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The smooth actual pole remainder internally produces both constants needed by the
relative physical-mobility estimate on one smaller unchanged endpoint neighborhood. -/
theorem exists_smooth_pole_remainder_bounds
    {ε : ℝ} (hε : 0<ε) {R : ℝ→Matrix ι ι ℝ}
    (hR : ContDiffOn ℝ ∞ R (Ioo (-ε) ε)) :
    ∃ δ : ℝ, δ>0 ∧ δ<ε ∧ ∃ M : ℝ, M≥0 ∧ ∃ N : ℝ, N≥0 ∧
      (∀s∈Icc (-δ) δ, ‖R s‖≤M) ∧
      ∀s∈Icc (-δ) δ, ∀t∈Icc (-δ) δ, ‖R s-R t‖≤N*|s-t| := by
  let δ := ε/2
  have hδ : 0<δ := half_pos hε
  have hδε : δ<ε := half_lt_self hε
  have hsub : Icc (-δ) δ ⊆ Ioo (-ε) ε := by
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  have hD : ContDiffOn ℝ ∞ (deriv R) (Ioo (-ε) ε) :=
    hR.deriv_of_isOpen isOpen_Ioo (by simp)
  obtain ⟨M₀,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hR.continuousOn.mono hsub)
  obtain ⟨N₀,hN⟩ := isCompact_Icc.exists_bound_of_continuousOn (hD.continuousOn.mono hsub)
  let M := max M₀ 0
  let N := max N₀ 0
  have hMbound : ∀s∈Icc (-δ) δ, ‖R s‖≤M :=
    fun s hs ↦ (hM s hs).trans (le_max_left _ _)
  have hNbound : ∀s∈Icc (-δ) δ, ‖deriv R s‖≤N :=
    fun s hs ↦ (hN s hs).trans (le_max_left _ _)
  have hdiff : ∀s∈Icc (-δ) δ, DifferentiableAt ℝ R s :=
    fun s hs ↦ (hR.contDiffAt (isOpen_Ioo.mem_nhds (hsub hs))).differentiableAt (by simp)
  refine ⟨δ,hδ,hδε,M,le_max_right _ _,N,le_max_right _ _,hMbound,fun s hs t ht ↦ ?_⟩
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hNbound (convex_Icc _ _) ht hs

end OTSelector.Reconstruction

end
end

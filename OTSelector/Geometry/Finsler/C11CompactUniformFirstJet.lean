import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FiniteTimeLipschitz
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11CompactUniformFirstJet.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11CompactUniformFirstJet`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.C11CompactUniformFirstJet

* **Conditions:** An actual complete C1,1 phase family and a compact original root–time set.
* **Objects:** A finite legal chart cover with one common bound for actual coordinate first derivatives and local Lipschitz constants.
* **Proof detail:** Take local chart Lipschitz estimates, shrink around each compact point, use differentiability bounds on their interiors and choose a finite cover/common maximum.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): A compact first-jet bound for the actual family, with the finite charts and constants explicitly constructed.
-/

/-! Actual C1,1 phase families have uniformly bounded first coordinate jets on
finite chart covers of every compact original root-time family. -/
open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal
noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
set_option maxHeartbeats 1200000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- One actual compact original root-time family admits a finite coordinate
cover with one first-jet bound. All output charts and constants are constructed
from the original C1,1 initial momentum and complete original Finsler flow. -/
theorem exists_compact_C11_uniform_firstJet_cover
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    {U K : Set E} (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ,E) initial).target)
    {Γ : E → ℝ → M}
    (hEL : ∀ x ∈ U, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ U, Γ x 0 = (extChartAt 𝓘(ℝ,E) initial).symm x)
    (hp : ∀ x ∈ U, F.chartMomentumFamily initial Γ (x,0) = (x,fderiv ℝ G x))
    {T : Set ℝ} (hT : IsCompact T) :
    let H := K ×ˢ T
    ∃ (J : Finset H) (radius : H → ℝ) (C : ℝ≥0), 0 < C ∧
      (∀ j ∈ J, 0 < radius j ∧
        closedBall (j : E × ℝ) (radius j) ⊆ U ×ˢ univ ∧
        MapsTo (fun p : E × ℝ ↦ Γ p.1 p.2) (closedBall (j : E × ℝ) (radius j))
          (extChartAt 𝓘(ℝ,E) (Γ j.val.1 j.val.2)).source ∧
        LipschitzOnWith C
          (fun p : E × ℝ ↦ extChartAt 𝓘(ℝ,E) (Γ j.val.1 j.val.2) (Γ p.1 p.2))
          (closedBall (j : E × ℝ) (radius j))) ∧
      (∀ p ∈ H, ∃ j ∈ J, p ∈ ball (j : E × ℝ) (radius j / 2) ∧
        ‖fderiv ℝ (fun z : E × ℝ ↦
          extChartAt 𝓘(ℝ,E) (Γ j.val.1 j.val.2) (Γ z.1 z.2)) p‖ ≤ C) := by
  classical
  let H := K ×ˢ T
  have hlocal (j : H) := hF.exists_joint_lipschitz_chart_readout_of_C11_initial_momentum
    hcomplete initial hG hLip hU hUt hEL hinit hp (hKU j.property.1)
      (Γ j.val.1 j.val.2) j.val.2 (mem_extChartAt_source _)
  choose radius c hr hsub hmap hLipLocal using hlocal
  have hcover : H ⊆ ⋃ j : H, ball (j : E × ℝ) (radius j / 2) := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,mem_ball_self (half_pos (hr ⟨p,hp⟩))⟩
  obtain ⟨J,hJ⟩ := (hK.prod hT).elim_finite_subcover
    (fun j : H ↦ ball (j : E × ℝ) (radius j / 2)) (fun _ ↦ isOpen_ball) hcover
  let C : ℝ≥0 := (∑ j ∈ J, c j) + 1
  have hc (j : H) (hj : j ∈ J) : c j ≤ C := by
    have hsum := Finset.single_le_sum (f := c) (fun _ _ ↦ bot_le) hj
    exact hsum.trans (by dsimp [C]; exact le_add_of_nonneg_right zero_le_one)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨J,radius,C,hC,?_,?_⟩
  · intro j hj
    exact ⟨hr j,hsub j,hmap j,(hLipLocal j).weaken (hc j hj)⟩
  · intro p hp
    obtain ⟨j,hj,hpj⟩ := mem_iUnion₂.mp (hJ hp)
    refine ⟨j,hj,hpj,?_⟩
    have hinside : p ∈ ball (j : E × ℝ) (radius j) :=
      ball_subset_ball (le_of_lt (half_lt_self (hr j))) hpj
    have hnhds : closedBall (j : E × ℝ) (radius j) ∈ 𝓝 p :=
      mem_of_superset (isOpen_ball.mem_nhds hinside) ball_subset_closedBall
    exact (norm_fderiv_le_of_lipschitzOn ℝ hnhds (hLipLocal j)).trans
      (show (c j : ℝ) ≤ C from hc j hj)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end

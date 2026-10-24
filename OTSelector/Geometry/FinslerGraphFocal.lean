import OTSelector.Analysis.ODE.Hamiltonian.GraphJacobiMatrix
import OTSelector.Geometry.FocalAsymptotics

/-!
# Regular focal rates for the actual Finsler graph variation

The true graph parameter derivative supplies the square position matrix. Its genuine
Hamiltonian equation, canonical isotropy and phase injectivity derive regular crossing.
At a singular point of positive kernel dimension, the determinant has that exact order
and the inverse operator norm has order one from either direction. Neither a crossing
condition nor nearby position invertibility is supplied as an extra hypothesis.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {W V ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M] {F : ContinuousFinslerNorm (ℝ × V) M}

/-- At each actual singular graph variation, the crossing is bijective and the
local determinant and inverse have the prescribed rates on both sides. -/
theorem chartGraph_regular_focal_bounds (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.chartGraphLagrangian x₀))
    (hsub : g.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field (F.chartGraphLagrangian x₀) g z.2 (Ψ z)) z.2)
    {w₀ : W} {t : ℝ} (hz : (w₀, t) ∈ D)
    (hp : ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target)
    (hinj : Function.Injective (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀))
    (hpair : ∀ u v : W, canonicalPhasePairing
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ u)
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ v) = 0) :
    let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀
    let J := fun s ↦ vectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).1)
    Function.Bijective (focalCrossingMap (J t) (deriv J t)) ∧
      (0 < Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) →
        ∀ ε : ℝ, ε = 1 ∨ ε = -1 → ∃ cdet Cdet cinv Cinv : ℝ,
          0 < cdet ∧ 0 < Cdet ∧ 0 < cinv ∧ 0 < Cinv ∧
          ∀ᶠ s in 𝓝[>] (0 : ℝ),
            cdet * |s| ^ Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) ≤
                |(J (t + ε * s)).det| ∧
              |(J (t + ε * s)).det| ≤
                Cdet * |s| ^ Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) ∧
              cinv / |s| ≤ ‖(J (t + ε * s))⁻¹‖ ∧
              ‖(J (t + ε * s))⁻¹‖ ≤ Cinv / |s|) := by
  dsimp only
  obtain ⟨hJ, _, _, _, hC, hW, hphase, _⟩ :=
    hF.chartGraph_parameter_matrices x₀ bW bV hg hsub hG hD hΨ hODE hz hp hinj hpair
  constructor
  · convert focalCrossingMap_bijective
      (B := hamiltonianMatrixB bV
        (GraphHamiltonian.blockB (F.chartGraphLagrangian x₀) g t (Ψ (w₀, t))))
      hW hphase hC using 1
    congr 1
    exact congrArg (focalCrossingMap _) hJ.deriv
  · intro hk ε hε
    rcases hε with rfl | rfl
    · simpa only [one_mul] using
        regular_focal_bounds_left_endpoint hJ.hasDerivWithinAt
          (fun u hu hr ↦ focal_crossing_kernel_eq_zero hW hphase hC hu hr) hk
    · simpa only [neg_mul, one_mul, sub_eq_add_neg] using
        regular_focal_bounds_right_endpoint hJ.hasDerivWithinAt
          (fun u hu hr ↦ focal_crossing_kernel_eq_zero hW hphase hC hu hr) hk

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

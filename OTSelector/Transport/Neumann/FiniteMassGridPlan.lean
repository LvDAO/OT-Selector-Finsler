import OTSelector.MeasureTheory.FiniteDensityCellReadout
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates
import OTSelector.Transport.Finite.ApproximateDualFiniteMass
import OTSelector.Transport.Neumann.QuadraticGridDualBound
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiFiniteMassGridPlan.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiFiniteMassGridPlan`; the selected original proof blocks follow. -/
section

/-!
Conditions: The same actual Neumann/compact-grid hypotheses and endpoint densities of a common strictly positive finite mass.

Objects: A nonnegative finite quadratic plan with exact original density-cell marginals and the stated unnormalized cost bound.

Proof detail: Apply finite-mass transport duality to every soft-dual bound and send the positive smoothing parameter to zero; keep the actual common mass in every error term.

Sources: Gabriel Peyré, Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31); Gabriel Peyré, Section 7.1, equations (7.1)–(7.5), pp. 112–113 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=116); Stephen Boyd, Section 3.1.5, pp. 72–74, log-sum-exp example and derivative calculation (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=86).
Relation: Finite-mass duality/action combination. Any normalization used in the proof is scaled back; the output plan and energy remain at the original mass.
-/

/-! Genuine quadratic finite plans at their original common positive mass, obtained
from the actual Neumann discrepancy and time-dependent soft tests. -/
open MeasureTheory Set TopologicalSpace
open scoped Distributions BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {ι I J : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype I] [Nonempty I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

/-- The original gradient discrepancy produces a genuine finite plan of the
literal original density cells without normalizing the final plan or energy budget. -/
theorem exists_originalDensity_quadratic_finiteMass_grid_plan
    (K : Compacts (ι→ℝ)) (μ : Measure (ι→ℝ)) [IsFiniteMeasure μ]
    {K₀ : Set (ι→ℝ)} (hK₀ : IsCompact K₀) (hK₀K : K₀⊆interior (K:Set (ι→ℝ)))
    (hμ : ∀ᵐx∂μ,x∈K₀) (f g : (ι→ℝ)→ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    {ρ C : ℝ} (hρ : 0<ρ) (hC : 0≤C)
    (hfl : ∀ᵐx∂μ,ρ≤f x) (hgl : ∀ᵐx∂μ,ρ≤g x)
    {mass : ℝ} (hmass : 0<mass)
    (hfmass : (∫z,f z∂μ)=mass) (hgmass : (∫z,g z∂μ)=mass)
    (hbound : ∀φ:𝓓_{K}(ι→ℝ,ℝ),
      ‖(∫x,φ x*f x∂μ)-(∫x,φ x*g x∂μ)‖≤C*‖smoothPhysicalGradientLtwo K μ φ‖)
    (T : (ι→ℝ)→I) (S : (ι→ℝ)→J) (hT : Measurable T) (hS : Measurable S)
    (x : I→(ι→ℝ)) (y : J→(ι→ℝ))
    {D h δ M : ℝ} (hD : 0≤D) (hh : 0≤h) (hδ : 0<δ)
    {Ω : Set (EuclideanSpace ℝ ι)} (hΩ : Convex ℝ Ω)
    (hnode : ∀z∈Ω,∀i,‖z-(EuclideanSpace.equiv ι ℝ).symm (x i)‖≤D)
    (hmem : ∀ᵐz∂μ,(EuclideanSpace.equiv ι ℝ).symm z∈Ω ∧
      (EuclideanSpace.equiv ι ℝ).symm (x (T z))∈Ω ∧
      (EuclideanSpace.equiv ι ℝ).symm (y (S z))∈Ω)
    (hdispT : ∀ᵐz∂μ,‖(EuclideanSpace.equiv ι ℝ).symm (x (T z))-
      (EuclideanSpace.equiv ι ℝ).symm z‖≤h)
    (hdispS : ∀ᵐz∂μ,‖(EuclideanSpace.equiv ι ℝ).symm (y (S z))-
      (EuclideanSpace.equiv ι ℝ).symm z‖≤h)
    (hcost : ∀i j,‖(EuclideanSpace.equiv ι ℝ).symm (y j)-
      (EuclideanSpace.equiv ι ℝ).symm (x i)‖^2/2≤M) :
    ∃P:I→J→ℝ,(∀i j,0≤P i j)∧
      (∀i,∑j,P i j=originalDensityCellWeight μ f T i)∧
      (∀j,∑i,P i j=originalDensityCellWeight μ g S j)∧
      (∑i,∑j,(‖(EuclideanSpace.equiv ι ℝ).symm (y j)-
        (EuclideanSpace.equiv ι ℝ).symm (x i)‖^2/2)*P i j)≤
        ρ⁻¹*C^2/2+mass*(D/(1+δ)*h+D/δ*h+M*δ) := by
  have hf0 : ∀ᵐz∂μ,0≤f z:=hfl.mono fun _ hz↦hρ.le.trans hz
  have hg0 : ∀ᵐz∂μ,0≤g z:=hgl.mono fun _ hz↦hρ.le.trans hz
  apply exists_finiteMassTransport_plan_le_of_soft_dual_bounds
    (originalDensityCellWeight μ f T) (originalDensityCellWeight μ g S)
    (fun i j↦‖(EuclideanSpace.equiv ι ℝ).symm (y j)-
      (EuclideanSpace.equiv ι ℝ).symm (x i)‖^2/2)
    (originalDensityCellWeight_nonneg μ f hf0 T) (originalDensityCellWeight_nonneg μ g hg0 S)
    hmass (by rw [sum_originalDensityCellWeight μ f hf T hT,hfmass])
    (by rw [sum_originalDensityCellWeight μ g hg S hS,hgmass])
    (ρ⁻¹*C^2/2+mass*(D/(1+δ)*h+D/δ*h+M*δ)) (mass*Real.log (Fintype.card I))
  intro ε hε u v hdual
  have hb:=originalDensity_quadratic_grid_dual_le K μ hK₀ hK₀K hμ f g hf hg hρ hC hfl hgl
    hbound T S hT hS x y hD hh hδ hε hΩ hnode hmem hdispT hdispS hcost u v hdual
  rw [hfmass,hgmass] at hb
  nlinarith only [hb]

end OTSelector.Reconstruction

end
end

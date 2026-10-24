import OTSelector.Analysis.Convex.TimeDependentSoftTests
import OTSelector.MeasureTheory.FiniteDensityCellReadout
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates
import OTSelector.Transport.Neumann.SoftFiniteDual
import OTSelector.Transport.Neumann.SoftGridError
import OTSelector.Transport.Neumann.SoftValueComparison
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiGridDualBound.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiGridDualBound`; the selected original proof blocks follow. -/
section

/-!
Conditions: Positive endpoint densities on a compact carrier, actual Neumann discrepancy bounds, finite measurable quantizers and all stated node/convex-domain/grid errors.

Objects: A price-independent bound on every actual finite quadratic dual objective, including explicit grid, time-shift and entropy errors.

Proof detail: Test the actual flux with the time-dependent quadratic soft minimum, bound endpoint quantization errors and use the finite dual endpoint inequalities.

Sources: Gabriel Peyré, Section 7.1, equations (7.1)–(7.5), pp. 112–113 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=116); Stephen Boyd, Section 3.1.5, pp. 72–74, log-sum-exp example and derivative calculation (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=86); Stephen Boyd, Section 3.3.2, Fenchel’s inequality and quadratic example, p. 94 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=108); Gabriel Peyré, Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31).
Relation: Locally derived finite-grid quantitative form of the Hamilton–Jacobi/Young method. The explicit error terms are not quoted as a textbook theorem.
-/

/-! The original Neumann discrepancy controls every finite quadratic dual of
its literal density cells, with an explicit price-independent grid error. -/
open MeasureTheory Set TopologicalSpace
open scoped Distributions BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {ι I J : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype I] [Nonempty I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

/-- Finite-cell quadratic duals consume the actual original-density Neumann
budget; quantization and soft endpoints contribute only explicit geometric errors. -/
theorem originalDensity_quadratic_grid_dual_le
    (K : Compacts (ι→ℝ)) (μ : Measure (ι→ℝ)) [IsFiniteMeasure μ]
    {K₀ : Set (ι→ℝ)} (hK₀ : IsCompact K₀) (hK₀K : K₀⊆interior (K:Set (ι→ℝ)))
    (hμ : ∀ᵐx∂μ,x∈K₀) (f g : (ι→ℝ)→ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    {ρ C : ℝ} (hρ : 0<ρ) (hC : 0≤C)
    (hfl : ∀ᵐx∂μ,ρ≤f x) (hgl : ∀ᵐx∂μ,ρ≤g x)
    (hbound : ∀φ:𝓓_{K}(ι→ℝ,ℝ),
      ‖(∫x,φ x*f x∂μ)-(∫x,φ x*g x∂μ)‖≤C*‖smoothPhysicalGradientLtwo K μ φ‖)
    (T : (ι→ℝ)→I) (S : (ι→ℝ)→J) (hT : Measurable T) (hS : Measurable S)
    (x : I→(ι→ℝ)) (y : J→(ι→ℝ))
    {D h δ ε M : ℝ} (hD : 0≤D) (hh : 0≤h) (hδ : 0<δ) (hε : 0<ε)
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
      (EuclideanSpace.equiv ι ℝ).symm (x i)‖^2/2≤M)
    (u : I→ℝ) (v : J→ℝ)
    (hdual : ∀i j,u i+v j≤‖(EuclideanSpace.equiv ι ℝ).symm (y j)-
      (EuclideanSpace.equiv ι ℝ).symm (x i)‖^2/2) :
    (∑i,originalDensityCellWeight μ f T i*u i)+(∑j,originalDensityCellWeight μ g S j*v j)≤
      ρ⁻¹*C^2/2+(D/(1+δ)*h)*(∫z,g z∂μ)+(D/δ*h)*(∫z,f z∂μ)+
        (∫z,g z∂μ)*(M*δ+ε*Real.log (Fintype.card I)) := by
  let nodes:=fun i↦(EuclideanSpace.equiv ι ℝ).symm (x i)
  let a:=fun i↦-u i
  let ψ:=neumannQuadraticSoftTest ε a nodes δ
  have hf0 : ∀ᵐz∂μ,0≤f z:=hfl.mono fun _ hz↦hρ.le.trans hz
  have hg0 : ∀ᵐz∂μ,0≤g z:=hgl.mono fun _ hz↦hρ.le.trans hz
  have hgridF:=neumannQuadraticSoftTest_grid_error μ hK₀ hμ f hf hf0
    (fun z↦x (T z)) ((measurable_of_finite x).comp hT) ε hε.ne' a nodes δ 0 D h
    (by simpa using hδ) hD hh hΩ hnode (hmem.mono fun _ hz↦⟨hz.1,hz.2.1⟩) hdispT
  have hgridG:=neumannQuadraticSoftTest_grid_error μ hK₀ hμ g hg hg0
    (fun z↦y (S z)) ((measurable_of_finite y).comp hS) ε hε.ne' a nodes δ 1 D h
    (by linarith) hD hh hΩ hnode (hmem.mono fun _ hz↦⟨hz.1,hz.2.2⟩) hdispS
  have hvalue:=originalDensity_neumannQuadraticSoft_signedValue_le K μ hK₀ hK₀K hμ
    f g hf hg hρ hC hfl hgl hbound hε.ne' hδ a nodes
  have hfinite:=neumannQuadraticSoftTest_weighted_dual_endpoints hε hδ.le
    (originalDensityCellWeight μ f T) (originalDensityCellWeight μ g S)
    (originalDensityCellWeight_nonneg μ f hf0 T) (originalDensityCellWeight_nonneg μ g hg0 S)
    u v x y hdual hcost
  dsimp only at hfinite
  simp_rw [originalDensityCellWeight_readout μ f hf T hT,
    originalDensityCellWeight_readout μ g hg S hS] at hfinite ⊢
  rw [sum_originalDensityCellWeight μ g hg S hS] at hfinite
  have hF:= (abs_sub_le_iff.mp hgridF.2.2).2
  have hG:= (abs_sub_le_iff.mp hgridG.2.2).1
  dsimp only [ψ,a,nodes] at hF hG hvalue
  simp only [zero_add] at hF
  linarith only [hfinite,hvalue,hF,hG]

end OTSelector.Reconstruction

end
end

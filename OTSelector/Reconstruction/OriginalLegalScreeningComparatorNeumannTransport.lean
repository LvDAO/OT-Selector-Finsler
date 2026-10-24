import OTSelector.Analysis.Sobolev.MeanZeroTestExtension
import OTSelector.Reconstruction.OriginalQuadraticTransportQuantizationNeumannEndpoint

/-! A true mean-zero Neumann estimate produces a genuine finite coupling of the
original densities, with the literal Euclidean full-square cost. -/
open MeasureTheory Set TopologicalSpace
open scoped Distributions Topology
noncomputable section
namespace OTSelector.Reconstruction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Centering with an actual cutoff and the existing finite-mass Neumann endpoint
construct the original transport plan. Its full-square budget uses the actual B. -/
theorem exists_originalDensity_quadratic_coupling_of_meanZero_squared_bound
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    {K₀ : Set (ι → ℝ)} (hK₀ : IsCompact K₀) (hK₀K : K₀ ⊆ interior (K : Set (ι → ℝ)))
    (χ : 𝓓_{K}(ι → ℝ, ℝ)) (hμ : ∀ᵐ z ∂μ, z ∈ K₀)
    (hχ : ∀ z ∈ K₀, (χ : (ι → ℝ) → ℝ) =ᶠ[𝓝 z] fun _ ↦ 1)
    (hμpos : 0 < μ.real univ) (f g : (ι → ℝ) → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hfl : ∀ᵐ z ∂μ, ρ ≤ f z) (hgl : ∀ᵐ z ∂μ, ρ ≤ g z)
    (hmass : (∫ z, f z ∂μ) = ∫ z, g z ∂μ)
    (hmean : ∀ ψ : 𝓓_{K}(ι → ℝ, ℝ), (∫ z, ψ z ∂μ) = 0 →
      |∫ z, ψ z * (f z-g z) ∂μ|^2 ≤ B*‖smoothPhysicalGradientLtwo K μ ψ‖^2) :
    ∀ ε : ℝ, 0 < ε → ∃ π : Measure ((ι → ℝ) × (ι → ℝ)),
      Vlasov.IsCoupling π (μ.withDensity (fun z ↦ ENNReal.ofReal (f z)))
        (μ.withDensity (fun z ↦ ENNReal.ofReal (g z))) ∧
      IsFiniteMeasure π ∧
      Integrable (fun z ↦ ‖(EuclideanSpace.equiv ι ℝ).symm z.2-
        (EuclideanSpace.equiv ι ℝ).symm z.1‖^2) π ∧
      (∫ z, ‖(EuclideanSpace.equiv ι ℝ).symm z.2-
        (EuclideanSpace.equiv ι ℝ).symm z.1‖^2 ∂π) ≤ ρ⁻¹*B+ε := by
  intro ε hε
  obtain ⟨π, hπ, hI, hc⟩ := exists_originalDensity_quadratic_epsilon_coupling
    K μ hK₀ hK₀K hμ f g hf hg hρ (Real.sqrt_nonneg B) hfl hgl hmass
    (all_test_bound_of_meanZero_squared_bound K μ K₀ χ hμ hχ hμpos
      f g hf hg hmass hB hmean) (ε/2) (by linarith)
  have : IsFiniteMeasure (π.map Prod.fst) := by
    rw [hπ.1]
    exact originalDensityWithDensity_isFiniteMeasure μ f hf (hfl.mono fun _ hz ↦ hρ.le.trans hz)
  have hfinite : IsFiniteMeasure π := Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable
  have hfullI : Integrable (fun z ↦ ‖(EuclideanSpace.equiv ι ℝ).symm z.2-
      (EuclideanSpace.equiv ι ℝ).symm z.1‖^2) π := by
    convert hI.const_mul 2 using 1
    ext z
    ring
  refine ⟨π, hπ, hfinite, hfullI, ?_⟩
  rw [Real.sq_sqrt hB] at hc
  have heq : (∫ z, ‖(EuclideanSpace.equiv ι ℝ).symm z.2-
        (EuclideanSpace.equiv ι ℝ).symm z.1‖^2 ∂π) =
      2*(∫ z, ‖(EuclideanSpace.equiv ι ℝ).symm z.2-
        (EuclideanSpace.equiv ι ℝ).symm z.1‖^2/2 ∂π) := by
    rw [← integral_const_mul]
    congr 1
    ext z
    ring
  rw [heq]
  linarith
end OTSelector.Reconstruction

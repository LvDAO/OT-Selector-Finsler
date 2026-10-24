import OTSelector.Reconstruction.FinslerPhysicalSceneRandomProbeFreezing
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedSubsequence
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMeanMarginals

/-!
# The original allocation experiment freezes its own full rooted probe

Original iid targets and original Dirichlet columns are unchanged. Actual
feasibility supplies the probability-mass bound required for expected freezing.
-/
open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped ENNReal Topology CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
local notation "V" => (ι → ℝ)

/-- The original feasible allocation produces the expected microscopic
freezing limit internally, on its own changing iid-target/Dirichlet experiment. -/
theorem tendsto_expected_original_allocation_macroProbeFreezingError_zero
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (alloc : ∀ n : ℕ,
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hfeas : ∀ n, ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ w.2 (alloc n w))
    (H : ℕ → Set M)
    (coord : ℕ → M → V) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    (η : C_c(V, ℝ)) (hη : ∀ v, 0 ≤ η v)
    (g : C_c(V × (ℝ × ℝ), ℝ)) (rootDomain : ℕ → Set V) :
    Tendsto (fun n ↦ ∫⁻ w, ∫⁻ z, physicalSceneMacroProbeFreezingError
      (physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ (alloc n) (fun w ↦ w.1) w).restrict (H n ×ˢ univ))
          (coord n) u ((n : ℝ) + 1) z) z (scale n) η g
        ∂cavityRootMeasure volume (rootDomain n) ((n : ℝ) + 1)
          ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)))
            atTop (𝓝 0) := by
  let Penv := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Γ := fun n w ↦
    (physicalSceneGlobalAllocationFamily μ (alloc n) (fun w ↦ w.1) w).restrict (H n ×ˢ univ)
  have hm : ∀ n, ∀ᵐ w ∂Penv n, Γ n w univ ≤ 1 := by
    intro n
    filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq (Penv n) μ (alloc n)
      (fun w ↦ w.1) (fun w ↦ w.2) (hfeas n), hfeas n] with w heq hw
    calc
      Γ n w univ ≤ physicalSceneGlobalAllocationFamily μ (alloc n) (fun w ↦ w.1) w univ :=
        Measure.restrict_le_self _
      _ = μ univ := by
        rw [heq, ← Measure.fst_univ, physicalSceneAllocationPlan_fst hw (w.1)]
      _ = 1 := measure_univ
  exact tendsto_expected_physicalSceneMacroProbeFreezingError_zero Penv (by intro n; simp [Penv])
    Γ hm (fun n _ ↦ coord n) (fun n _ ↦ hcoord n) u hu
    (fun n ↦ (n : ℝ) + 1) (fun n ↦ by positivity)
    scale hscalePos hscale η hη g (fun n _ ↦ rootDomain n)

end OTSelector.Reconstruction

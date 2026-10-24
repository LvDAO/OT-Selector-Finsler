import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationPlanTight
import OTSelector.Probability.ProbabilityMeasureWeakSecondCountable
import OTSelector.Probability.CommonIteratedWeakSubsequence

/-!
# Two original global plan-law limits without a new experiment

The weak Borel and Giry structures agree. Original compact supports then
supply both sample and tilt weak limits of the unchanged paired plan laws.
-/
open Set Function Filter MeasureTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ProperSpace M] [PolishSpace M]
local instance originalGlobalPlanProbabilitySecondCountable :
    SecondCountableTopology (ProbabilityMeasure (M × M)) := probabilityMeasure_weakSecondCountable
local instance originalGlobalPlanProbabilityBorel : BorelSpace (ProbabilityMeasure (M × M)) :=
  probabilityMeasure_weakBorelSpace

/-- Actual original feasible allocations admit separate sample and tilt
weak-law limits. The same original input experiment realizes both plans. -/
theorem exists_iterated_originalAllocationPlanPairLaw
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (Renv : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (Renv n)]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : ∀ (_ℓ n : ℕ), Ωn n → M → Fin (m n + 1) → ℝ)
    (hpm : ∀ ℓ n k, Measurable (fun z : Ωn n × M ↦ ap ℓ n z.1 z.2 k))
    (hmm : ∀ ℓ n k, Measurable (fun z : Ωn n × M ↦ am ℓ n z.1 z.2 k))
    (Y : ∀ n, Ωn n → Fin (m n + 1) → M)
    (hY : ∀ n k, Measurable (fun w ↦ Y n w k))
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (hfp : ∀ ℓ n, ∀ᵐ w ∂Renv n, IsSemidiscreteAllocation μ (p n w) (ap ℓ n w))
    (hfm : ∀ ℓ n, ∀ᵐ w ∂Renv n, IsSemidiscreteAllocation μ (p n w) (am ℓ n w))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hYB : ∀ n, ∀ᵐ w ∂Renv n, ∀ k, Y n w k ∈ B) :
    let laws := fun ℓ n ↦ physicalSceneOriginalAllocationPlanPairLaw (Renv n) μ ν
      (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (Y n) (hY n)
    ∃ Q : ℕ → ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)),
      ∃ φ : ℕ → ℕ → ℕ, (∀ ℓ, StrictMono (φ ℓ)) ∧
        (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) ∧
        ∃ R : ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)),
          ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R) := by
  intro laws
  have htight := isTightMeasureSet_originalAllocationPlanPairLaw
    (fun s : ℕ × ℕ ↦ m s.2) (fun s : ℕ × ℕ ↦ Renv s.2) μ ν
    (fun s ↦ ap s.1 s.2) (fun s ↦ am s.1 s.2)
    (fun s ↦ hpm s.1 s.2) (fun s ↦ hmm s.1 s.2)
    (fun s ↦ Y s.2) (fun s ↦ hY s.2) (fun s ↦ p s.2)
    (fun s ↦ hfp s.1 s.2) (fun s ↦ hfm s.1 s.2) hA hB hμA (fun s ↦ hYB s.2)
  obtain ⟨Q, φ, hφ, hinner, R, ψ, hψ, houter⟩ :=
    exists_common_iterated_probabilityMeasure_subseq_of_isTight
      (fun _ : Unit ↦ laws) (fun _ ↦ htight)
  exact ⟨Q (), φ, hφ, hinner (), R (), ψ, hψ, houter ()⟩

end OTSelector.Reconstruction

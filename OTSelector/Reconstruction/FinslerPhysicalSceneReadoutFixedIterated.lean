import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutIteratedMarginals

/-!
# Both weak-limit stages for the same given physical potential

Actual globally feasible original allocation families and their same-potential
energy construct sample-size weak limits at every fixed tilt, then an outer
tilt-index limit. The resulting law retains the same countable target carrier,
a positive original support clock gap, and locally finite full marginals for both
plans. No weak-limit existence premise is supplied.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M : Type*} [Fintype ι]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
variable (base : (ι → ℝ) × ℝ)
local instance physicalSceneFixedIteratedStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance physicalSceneFixedIteratedConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance physicalSceneFixedIteratedConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance physicalSceneFixedIteratedConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance physicalSceneFixedIteratedPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

/-- Feasible global families for one given original potential and their actual
energy construct both weak-limit stages, legality and all marginal local finiteness. -/
theorem exists_given_potential_iterated_legal_scene_locallyFinite_marginals
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (u : M → ℝ) (hu : LipschitzWith 1 u)
    (scale : ℕ → ℝ) (hsp : ∀ n, 0 < scale n) (hsTop : Tendsto scale atTop atTop)
    (aplus aminus : ∀ (_ℓ n : ℕ), ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) →
      M → Fin (n + 1) → ℝ)
    (hplus : ∀ ℓ n j, Measurable (fun z : (((Fin (n + 1) → M) ×
      (Fin (n + 1) → ℝ)) × M) ↦ aplus ℓ n z.1 z.2 j))
    (hminus : ∀ ℓ n j, Measurable (fun z : (((Fin (n + 1) → M) ×
      (Fin (n + 1) → ℝ)) × M) ↦ aminus ℓ n z.1 z.2 j))
    (hfp : ∀ ℓ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (aplus ℓ n z))
    (hfm : ∀ ℓ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (aminus ℓ n z))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hep : ∀ ℓ n, (∫⁻ z, ∫⁻ e, ENNReal.ofReal
      (scale n * (dist e.1 (z.1 e.2) - u (z.1 e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aplus ℓ n z)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C)
    (hem : ∀ ℓ n, (∫⁻ z, ∫⁻ e, ENNReal.ofReal
      (scale n * (dist e.1 (z.1 e.2) - u (z.1 e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aminus ℓ n z)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C) :
        ∀ (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
          (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
          (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((n : ℝ) + 1)),
        ∃ Q : ℕ → ProbabilityMeasure
            (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base),
        ∃ φ : ℕ → ℕ → ℕ,
          (∀ ℓ, StrictMono (φ ℓ) ∧
            Tendsto (fun k ↦ actualAllocationRootedCountableSceneLaw base
              ((Measure.pi (fun _ : Fin (φ ℓ k + 1) ↦ ν)).prod (dirichletOne (φ ℓ k))) μ
              (aplus ℓ (φ ℓ k)) (aminus ℓ (φ ℓ k)) (hplus ℓ (φ ℓ k)) (hminus ℓ (φ ℓ k))
              (fun z ↦ z.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
              (H (φ ℓ k)) (hH (φ ℓ k)) (coord (φ ℓ k)) (hcoord (φ ℓ k))
              u hu.continuous.measurable (D (φ ℓ k)) (hD (φ ℓ k))) atTop (𝓝 (Q ℓ))) ∧
          ∃ R, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (Q ∘ ψ) atTop (𝓝 R) ∧
          ∃ gap > 0, ∀ᵐ s ∂(R : Measure
            (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
            (Function.support (LocalConfiguration.multiplicity s.2)).Countable ∧
            (∀ᵐ e ∂(s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
              e.2 ∈ Function.support (LocalConfiguration.multiplicity s.2) ∧
                gap / 2 ≤ e.2.2 - e.1.2) ∧
            (∀ᵐ e ∂(s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
              e.2 ∈ Function.support (LocalConfiguration.multiplicity s.2) ∧
                gap / 2 ≤ e.2.2 - e.1.2) ∧
            IsFiniteMeasureOnCompacts
              (s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).fst ∧
            IsFiniteMeasureOnCompacts
              (s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).fst ∧
            IsFiniteMeasureOnCompacts
              (s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).snd ∧
            IsFiniteMeasureOnCompacts
              (s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).snd := by
  intro H hH coord hcoord D hD
  let Ω := fun n ↦ (Fin (n + 1) → M) × (Fin (n + 1) → ℝ)
  let Penv : ∀ n, Measure (Ω n) := fun n ↦
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  obtain ⟨Q, φ, hinner, R, ψ, hψ, houter, hcarrier⟩ :=
    exists_iterated_actualAllocationRootedCountableSceneLaw base id Penv μ
      aplus aminus hplus hminus (fun _ z ↦ z.1)
      (fun _ j ↦ (measurable_pi_apply j).comp measurable_fst) (fun _ z ↦ z.2)
      hfp hfm H hH coord hcoord u hu.continuous.measurable D hD
  obtain ⟨gap, hgap, hclock⟩ := ae_iterated_actualAllocationRootedScene_clock_gap base
    id Penv μ ν hA hB hAB hμ hν aplus aminus hplus hminus
    (fun _ z ↦ z.1) (fun _ j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun n j ↦ physicalSceneOriginalDirichlet_target_law ν n j) (fun _ z ↦ z.2)
    hfp hfm H hH coord hcoord hu scale hsp hsTop D hD C hC hep hem
    Q φ (fun ℓ ↦ (hinner ℓ).1) (fun ℓ ↦ (hinner ℓ).2) R ψ houter
  have hsource := ae_iterated_actualAllocationRootedScene_source_locallyFinite base
    id Penv μ aplus aminus hplus hminus (fun _ z ↦ z.1)
    (fun _ j ↦ (measurable_pi_apply j).comp measurable_fst) (fun _ z ↦ z.2)
    hfp hfm H hH coord hcoord u hu.continuous.measurable D hD
    Q φ (fun ℓ ↦ (hinner ℓ).2) R ψ houter
  have htarget := ae_iterated_actualAllocationRootedScene_target_locallyFinite base
    id Penv μ aplus aminus hplus hminus (fun _ z ↦ z.1)
    (fun _ j ↦ (measurable_pi_apply j).comp measurable_fst) (fun _ z ↦ z.2)
    hfp hfm H hH coord hcoord u hu.continuous.measurable D hD
    Q φ (fun ℓ ↦ (hinner ℓ).2) R ψ houter
  refine ⟨Q, φ, hinner, R, ψ, hψ, houter, gap, hgap, ?_⟩
  filter_upwards [hcarrier, hclock, hsource, htarget] with s hs hc hf ht
  exact ⟨hs.1, hs.2.1.and hc.1, hs.2.2.and hc.2, hf.1, hf.2, ht.1, ht.2⟩

end OTSelector.Reconstruction

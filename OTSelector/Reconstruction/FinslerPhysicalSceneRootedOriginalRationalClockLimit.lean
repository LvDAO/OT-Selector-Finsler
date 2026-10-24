import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedClockNullLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalClockCollar
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedJoint

/-! Actual original population densities remove every rational clock boundary in one AE event. -/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)
local instance originalRationalClockLimitStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalRationalClockLimitConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance originalRationalClockLimitConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalRationalClockLimitConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalRationalClockLimitPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "Edge" => (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

open Manifold OTSelector.Geometry
open scoped ContDiff
variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  [IsFiniteMeasure lambda] {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ}

/-- The original physical density and globally feasible allocation families
produce a common probability-one event with no rational clock levels in either
full limiting plan. Only the original experiment and its two weak stages occur. -/
theorem PopulationConditionalWindowLaw.ae_originalAllocation_full_rational_clock_null_of_iterated
    (hμlaw : PopulationConditionalWindowLaw P a κ lambda μ ρ₀ v)
    (hνlaw : PopulationConditionalWindowLaw P a κ lambda ν ρ₁ v)
    (ha : Measurable a) (hu : Measurable u)
    (ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 j))
    (hmm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 j))
    (hp : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (ap ℓ n w))
    (hm : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (am ℓ n w))
    (H : Set M) (hH : MeasurableSet H) (Egood : Set (M × M)) (hEgood : MeasurableSet Egood)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (scale : ℕ → ℝ) (rootDomain : ℕ → Set (ι → ℝ))
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1)) :
    let laws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦
      actualAllocationRootedMaskedMacroscopicSceneLaw base
        ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
        (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
        (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
        H hH Egood hEgood (coord n) (hcoord n) u hu (scale n)
        (rootDomain n) (hrootDomain n)
    ∀ (Q : ℕ → ProbabilityMeasure JointScene) (R : ProbabilityMeasure JointScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) → ∀ ψ : ℕ → ℕ,
      Tendsto ψ atTop atTop →
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R) →
      ∀ᵐ s ∂(R : Measure JointScene), ∀ q : ℚ,
        (s.1.2.1.1 : Measure Edge) {e | e.1.2 = (q : ℝ) ∨ e.2.2 = (q : ℝ)} = 0 ∧
        (s.1.2.1.2 : Measure Edge) {e | e.1.2 = (q : ℝ) ∨ e.2.2 = (q : ℝ)} = 0 := by
  classical
  dsimp only
  intro Q R φ hφ ψ hψ hinner houter
  apply ae_all_iff.mpr
  intro q
  let thresholds : Finset ℝ := {(q : ℝ)}
  let B : Set (ℝ × ℝ) :=
    ((↑thresholds : Set ℝ) ×ˢ univ) ∪ (univ ×ˢ (↑thresholds : Set ℝ))
  let collar : ℕ → Set (ℝ × ℝ) := fun m ↦
    (Metric.thickening (1 / ((m : ℝ) + 1)) (↑thresholds : Set ℝ) ×ˢ univ) ∪
      (univ ×ˢ Metric.thickening (1 / ((m : ℝ) + 1)) (↑thresholds : Set ℝ))
  have hB : MeasurableSet B :=
    (thresholds.finite_toSet.measurableSet.prod MeasurableSet.univ).union
      (MeasurableSet.univ.prod thresholds.finite_toSet.measurableSet)
  have hcollar (m : ℕ) : IsOpen (collar m) :=
    (Metric.isOpen_thickening.prod isOpen_univ).union
      (isOpen_univ.prod Metric.isOpen_thickening)
  have hsub (m : ℕ) : B ⊆ collar m := by
    intro p hp
    have hs := Metric.self_subset_thickening
      (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1)) (↑thresholds : Set ℝ)
    exact hp.elim (fun h ↦ Or.inl ⟨hs h.1, h.2⟩) (fun h ↦ Or.inr ⟨h.1, hs h.2⟩)
  let error : ℕ → ℝ≥0∞ := fun m ↦
    μ (originalClockEndpointCollar u thresholds (1 / ((m : ℝ) + 1))) +
      ν (originalClockEndpointCollar u thresholds (1 / ((m : ℝ) + 1)))
  have herror : Tendsto error atTop (𝓝 0) := by
    have hμ := tendsto_originalClockEndpointCollar μ hu thresholds
      (fun p _ ↦ hμlaw.original_clock_level_null ha hu p)
    have hν := tendsto_originalClockEndpointCollar ν hu thresholds
      (fun p _ ↦ hνlaw.original_clock_level_null ha hu p)
    simpa only [add_zero] using hμ.add hν
  have hmass (m ℓ n : ℕ)
      (A : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
      (hA : ∀ j, Measurable (fun z :
        ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ A z.1 z.2 j))
      (hfeas : ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (A w)) :
      (∫⁻ w, physicalSceneGlobalAllocationFamily μ A (fun w ↦ w.1) w
        ((fun p : M × M ↦ (u p.1, u p.2)) ⁻¹' collar m)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ error m := by
    apply (lintegral_mono fun w ↦ measure_mono ?_).trans
      (lintegral_originalAllocation_clockEndpointCollar_le μ ν n A hA hfeas hu thresholds _)
    intro p hp
    have hs := Metric.thickening_subset_cthickening
      (1 / ((m : ℝ) + 1)) (↑thresholds : Set ℝ)
    exact hp.elim (fun h ↦ Or.inl ⟨hs h.1, h.2⟩) (fun h ↦ Or.inr ⟨h.1, hs h.2⟩)
  have hzero := ae_full_original_clock_null_of_iterated_actual_masked_scene base
    (fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
    (fun ℓ n ↦ physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1))
    (fun ℓ n ↦ physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1))
    (fun ℓ n ↦ measurable_physicalSceneGlobalAllocationFamily μ (ap ℓ n) (hpm ℓ n)
      (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst))
    (fun ℓ n ↦ measurable_physicalSceneGlobalAllocationFamily μ (am ℓ n) (hmm ℓ n)
      (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst))
    H hH Egood hEgood coord hcoord u hu scale
    (fun _ w ↦ w.1) (fun _ j ↦ (measurable_pi_apply j).comp measurable_fst)
    rootDomain hrootDomain B hB collar hcollar hsub error herror
    (fun m ℓ n ↦ hmass m ℓ n (ap ℓ n) (hpm ℓ n) (hp ℓ n))
    (fun m ℓ n ↦ hmass m ℓ n (am ℓ n) (hmm ℓ n) (hm ℓ n))
    Q R φ hφ ψ hψ hinner houter
  filter_upwards [hzero] with s hs
  have heq : {e : Edge | (e.1.2, e.2.2) ∈ B} =
      {e | e.1.2 = (q : ℝ) ∨ e.2.2 = (q : ℝ)} := by
    ext e
    simp only [B, thresholds, Finset.coe_singleton, mem_ofPred_eq, mem_union,
      mem_prod, mem_univ, and_true, true_and, mem_singleton_iff]
  rw [heq, LocalFiniteMeasure.coe_cavityAverage, Measure.smul_apply, smul_eq_mul,
    Measure.add_apply] at hs
  exact add_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left (by norm_num))
end OTSelector.Reconstruction

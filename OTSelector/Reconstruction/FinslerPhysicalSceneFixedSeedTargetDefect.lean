import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeed
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCrossingTargetDefect

/-!
# Actual target defects in one fixed original seed scene

The physical source piece and coordinate frame remain fixed while auxiliary
accuracy cores vary only the estimate.  Crossings of that same original seed
piece lie in every auxiliary global non-near event, whose original population
losses and true scaled energy control the actual restricted target-test defect.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] {μ ν : Measure M}
  [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞} [∀ j, SigmaFinite (κ j)]

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  (horder : let _inst : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
include hF hcomplete hu ha hinj horder

/-- The same actual fixed-seed source restriction has target-test defect paid
by the original auxiliary population losses and true global energy.  Neither
the physical scene nor its exact restricted columns depends on that accuracy. -/
theorem exists_original_fixed_seed_target_test_defect_bounds
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ (j n : ℕ)
      (aplus aminus : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
      (_hplus : ∀ k, Measurable
        (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦ aplus z.1 z.2 k))
      (_hminus : ∀ k, Measurable
        (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦ aminus z.1 z.2 k)),
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (aplus z)) →
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (aminus z)) →
      ∀ (spatialScale N : ℝ), 0 < spatialScale → 0 < N →
      ∀ (rootDomain U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)),
      MeasurableSet U → ∀ (f : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ, ℝ)),
      (∀ y ∈ tsupport f, y.1 ∈ U) → ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ aplus (fun z ↦ z.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ aminus (fun z ↦ z.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
      (∫⁻ w, ∫⁻ z, ENNReal.ofReal
        |(∫ e, f e.2 ∂physicalSceneRootedPlan
            ((physicalSceneGlobalAllocationFamily μ aplus (fun z ↦ z.1) w).restrict (H ×ˢ univ))
            coord u N z) -
          ∫ e, f e.2 ∂physicalSceneRootedPlan
            ((physicalSceneGlobalAllocationFamily μ aminus (fun z ↦ z.1) w).restrict (H ×ˢ univ))
            coord u N z|
        ∂cavityRootMeasure volume rootDomain N
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      2 * ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U *
        (μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
          C / ENNReal.ofReal (spatialScale ^ 2 * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨c, hc, hmass⟩ := D.exists_original_nonNear_mass_bound
    hF hcomplete hu ha hinj horder hA hB hgap hdist (show (0 : ℝ) < 1 by norm_num) hwindow
  refine ⟨c, hc, ?_⟩
  intro j n aplus aminus hplus hminus hfp hfm spatialScale N hsp hN
    rootDomain U hU f hfU C hEp hEm
  dsimp only
  let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
  let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
  have hH : MeasurableSet H := measurableSet_physicalSceneOriginalSeedSource
    hF hcomplete hu ha hinj j
  have hcoord : Measurable coord := measurable_physicalSceneOriginalSeedScaledPosition
    hF hcomplete hu ha hinj j spatialScale
  have hYB : ∀ᵐ w ∂Penv, ∀ k, w.1 k ∈ B := by
    apply ae_all_iff.mpr
    intro k
    have hm : Measurable (fun w : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) ↦ w.1 k) :=
      (measurable_pi_apply k).comp measurable_fst
    apply ae_of_ae_map (p := fun y : M ↦ y ∈ B) hm.aemeasurable
    rw [show Penv.map (fun w ↦ w.1 k) = ν from physicalSceneOriginalDirichlet_target_law ν n k]
    exact hνB
  have hcover : (A ×ˢ B) ∩ physicalSceneCoreCrossing H ⊆
      (A ×ˢ B) \ ⋃ i, D.nearDisplacementEvent i 1 := by
    simpa only [physicalSceneCoreCrossing, inter_comm] using
      D.fixed_seed_crossing_subset_global_nonNear j A B 1
  exact lintegral_actualAllocation_rooted_target_tests_le_covering_event
    Penv μ aplus aminus hplus hminus (fun z ↦ z.1)
    (fun k ↦ (measurable_pi_apply k).comp measurable_fst) (fun z ↦ z.2) hfp hfm
    hA hB hμA hYB H hH _ hcover _
    (hmass n aplus hplus hfp (spatialScale ^ 2) (sq_pos_of_pos hsp) C hEp)
    (hmass n aminus hminus hfm (spatialScale ^ 2) (sq_pos_of_pos hsp) C hEm)
    coord hcoord u hu.continuous.measurable N hN rootDomain U hU f hfU

end PopulationLocalPressureCore
end OTSelector.Reconstruction

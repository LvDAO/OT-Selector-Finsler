import OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceTestEscape
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceCutoffDefect

/-!
# Actual original source compact-test cutoff bounds

Both original allocations use the same original targets, masses, physical
source restriction and rooted coordinates.  Their original global energy bounds
produce the actual compact product-test estimate under their common scene law.
The canonical compact exhaustion is chosen before the sample size and either
allocation, while both original population losses remain explicit.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace
open OTSelector.Probability
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

/-- The same actual pair scene law has compact source-test defect bounded by
its true energy tails and the two original population complement masses.
All cutoff choices precede the original sample and both feasible allocations. -/
theorem exists_original_allocation_source_cutoff_defect_bounds
    {A B : Set M} (hA : MeasurableSet A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ q > 0, ∃ c > 0, ∀ (i : Fin D.haar.continuous.count)
      (f : C_c((Fin (finrank ℝ
        (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ) × ℝ, ℝ)),
    ∃ W clockBound : ℝ,
      ∀ (n : ℕ)
        (aplus aminus : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
        (hplus : ∀ j, Measurable
          (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦ aplus z.1 z.2 j))
        (hminus : ∀ j, Measurable
          (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦ aminus z.1 z.2 j)),
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (aplus z)) →
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (aminus z)) →
      ∀ (H : Set M) (hH : MeasurableSet H), H ⊆ D.physicalCoreDomain i →
      ∀ (spatialScale N : ℝ), 0 < spatialScale → ∀ (hN : 0 < N),
      ∀ (rootDomain : Set
        (Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ))
        (hRoot : volume rootDomain = ENNReal.ofReal N) (m : ℕ) (C : ℝ≥0∞),
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ aplus (fun z ↦ z.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ aminus (fun z ↦ z.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      let coord := D.scaledPhysicalBasisPosition i spatialScale
      let hcoord := D.measurable_scaledPhysicalBasisPosition hF hcomplete hu ha hinj i spatialScale
      let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
      let g := LocalFiniteMeasure.exhaustionCutoff (physicalSceneSpatialClockExhaustion W clockBound) m
      (∫⁻ scene : CavityLocalScene
          ((Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ) × ℝ)
          ((Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ) × ℝ),
        ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1 (cavityProductTest f g) -
          LocalFiniteMeasure.testIntegral scene.2 (cavityProductTest f g)|
        ∂(actualAllocationRootedSceneLaw Penv μ aplus aminus hplus hminus
          (fun z ↦ z.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
          H hH coord hcoord u (by
            let _inst : MetricSpace M := F.metricSpace
            exact hu.continuous.measurable) N hN rootDomain hRoot : Measure _)) ≤
      2 * ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        ((volume (physicalSceneTestSpatialWindow f) * (C / ENNReal.ofReal q)) /
          ENNReal.ofReal (((m : ℝ) + 1) ^ 2) +
        volume (physicalSceneTestSpatialWindow f) *
          (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ +
            C / ENNReal.ofReal (spatialScale ^ 2 * c))) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨q, hq, c, hc, hescape⟩ := D.exists_original_allocation_source_test_escape_bounds
    hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist hwindow
  refine ⟨q, hq, c, hc, ?_⟩
  intro i f
  obtain ⟨W, clockBound, htail⟩ := hescape i f
  refine ⟨W, clockBound, ?_⟩
  intro n aplus aminus hplus hminus hfp hfm H hH hHsub spatialScale N hsp hN
    rootDomain hRoot m C hEp hEm
  dsimp only
  let K := physicalSceneSpatialClockExhaustion (ι :=
    Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)) W clockBound
  let g := LocalFiniteMeasure.exhaustionCutoff K m
  let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let coord := D.scaledPhysicalBasisPosition i spatialScale
  have hcoord := D.measurable_scaledPhysicalBasisPosition hF hcomplete hu ha hinj i spatialScale
  have hbound := lintegral_actualAllocationRootedSceneLaw_source_cutoff_defect_le_escape
    Penv μ aplus aminus hplus hminus (fun z ↦ z.1)
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst) (fun z ↦ z.2)
    hfp hfm H hH coord hcoord u hu.continuous.measurable N hN rootDomain hRoot
    f g (LocalFiniteMeasure.exhaustionCutoff_bounds K m) (K m) (K.isCompact m).measurableSet
    (fun _ hx ↦ LocalFiniteMeasure.exhaustionCutoff_eq_one K m hx)
  have htailp := htail n aplus hplus hfp H hH hHsub spatialScale N hsp hN rootDomain hRoot m C hEp
  have htailm := htail n aminus hminus hfm H hH hHsub spatialScale N hsp hN rootDomain hRoot m C hEm
  exact hbound.trans ((mul_le_mul_right (add_le_add htailp htailm) _).trans_eq (by ring))

end PopulationLocalPressureCore
end OTSelector.Reconstruction

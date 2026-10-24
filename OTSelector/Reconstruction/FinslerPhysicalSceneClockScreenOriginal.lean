import OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceScalarTails
import OTSelector.Reconstruction.FinslerPhysicalSceneClockScreenLocal

/-!
# One original physical core with small clock screens and population tails

The same original optimal face produces its actual conditional forward clock
couplings. Its original Haar recovery then constructs a local core with all
clock screens below any positive threshold and both population complements
controlled by the prescribed original losses.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open OTSelector.Probability
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

section OriginalCore
open Manifold OTSelector.Geometry
open scoped ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}

/-- The same original optimal face produces one actual local core whose clock
screens all fit any prescribed positive threshold, while both original physical
population complements remain at most the specified root and scalar losses. -/
theorem exists_original_small_clock_screen_population_core_of_face
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ x ∂ν, x ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {θ : ℝ} (hθ : 0 < θ) {δ loss : ℝ≥0∞} (hδ : δ ≠ 0) (hloss : loss ≠ 0) :
    ∃ D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (fun z ↦ ∃ π : Measure (ℝ × ℝ),
        Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) ∧
          ∀ᵐ p ∂π, p.1 ≤ p.2) r δ loss,
      (∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ θ) ∧
      μ (⋃ i, D.physicalCoreDomain i)ᶜ ≤ loss + δ ∧
      ν (⋃ i, D.physicalCoreDomain i)ᶜ ≤ loss + δ := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instBorel : StandardBorelSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  have hlegal := ae_original_conditional_clock_forward_coupling_of_face μ ν
    hA hB hμ hν u hu.continuous.measurable a hbalance (fun π hπ ↦ (hface π).mp hπ)
  obtain ⟨D, hscreen⟩ := hcore.exists_local_core_small_clock_screen hrecovery hF hcomplete
    hu ha hinj hκ hlegal hθ hδ hloss
  have hgood (i : Fin D.haar.continuous.count) (z : ℚ → M)
      (hz : z ∈ (D.haar.continuous.coefficient i).roots) :
      ∃ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π (condDistrib u a μ z)
        (condDistrib u a ν z) ∧ ∀ᵐ p ∂π, p.1 ≤ p.2 := by
    have hroot : z ∈ D.haar.continuous.population.roots := by
      rw [← D.haar.continuous.union_eq]
      exact mem_iUnion.mpr ⟨i, hz⟩
    exact (D.haar.continuous.population.good z hroot).1
  refine ⟨D, hscreen, ?_, ?_⟩
  · have hs := D.original_source_outside_physical_cores_le hcomplete hu.continuous.measurable
      ha hμreg hgood
    simpa only [Measure.map_apply ha MeasurableSet.univ, preimage_univ, measure_univ, mul_one] using hs
  · have ht := D.original_target_outside_physical_cores_le hcomplete hu.continuous.measurable
      ha hreg hgood
    simpa only [Measure.map_apply ha MeasurableSet.univ, preimage_univ, measure_univ, mul_one] using ht

end OriginalCore
end OTSelector.Reconstruction

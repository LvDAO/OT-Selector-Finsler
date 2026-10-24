import OTSelector.Reconstruction.FinslerPhysicalSceneRootedScalarTails

/-!
# Conditional clock coupling from the same original optimal face

The actual compact-carrier original optimum produces its own forward conditional
clock coupling. The same potential, label law and actual local core then control
the discarded physical target mass.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Metric OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction

section ClockCoupling
variable {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z] [MeasurableEq Z]

omit [MeasurableEq Z] in
/-- The original compact-carrier optimal face supplies actual conditional
forward clock couplings on its own label law. -/
theorem ae_original_conditional_clock_forward_coupling_of_face
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A B N : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (u : M → ℝ) (hu : Measurable u) (a : M → Z) (hbalance : μ.map a = ν.map a)
    (hface : ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π →
      ∃ k : Kernel Z (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
        ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
          (condDistrib id a μ z) (condDistrib id a ν z) ∧
          ∀ᵐ p ∂k z, p.1 ∈ N ∧ p.2 ∈ N ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2) :
    ∀ᵐ z ∂μ.map a, ∃ π : Measure (ℝ × ℝ),
      Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) ∧
        ∀ᵐ p ∂π, p.1 ≤ p.2 := by
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling_edist_of_compact_carrier μ ν (hA.union hB)
    (hμ.mono fun _ hx ↦ Or.inl hx) (hν.mono fun _ hx ↦ Or.inr hx)
  obtain ⟨k, _hk, _hcomp, hκ⟩ := hface π hπ
  have hc₀ := ae_condDistrib_clock_eq_map_id μ a hu
  have hc₁ := ae_condDistrib_clock_eq_map_id ν a hu
  rw [← hbalance] at hc₁
  filter_upwards [hκ, hc₀, hc₁] with z hz h₀ h₁
  refine ⟨(k z).map (Prod.map u u), ?_, ?_⟩
  · rw [h₀, h₁]
    exact hz.1.map u u hu hu
  · apply (ae_map_iff (hu.prodMap hu).aemeasurable
      (measurableSet_le measurable_fst measurable_snd)).mpr
    exact hz.2.mono fun _ hp ↦ hp.2.2.2

end ClockCoupling

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

/-- The same original optimal-face and local-core producers construct a physical
core with target complement at most the two prescribed original losses. The
conditional legal coupling is constructed internally from the original face. -/
theorem exists_original_core_small_physical_target_tail_of_face
    (hcore : PopulationLocalPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a) (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ x ∂ν, x ∈ F.potentialRegularDomain u)
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
    {δ loss : ℝ≥0∞} (hδ : δ ≠ 0) (hloss : loss ≠ 0) :
    ∃ D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (fun z ↦ ∃ π : Measure (ℝ × ℝ),
        Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) ∧
          ∀ᵐ p ∂π, p.1 ≤ p.2) r δ loss,
      ν (⋃ i, D.physicalCoreDomain i)ᶜ ≤ loss + δ := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instBorel : StandardBorelSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  have hlegal := ae_original_conditional_clock_forward_coupling_of_face μ ν
    hA hB hμ hν u hu.continuous.measurable a hbalance (fun π hπ ↦ (hface π).mp hπ)
  obtain ⟨D, htail⟩ := exists_original_core_small_physical_target_tail hcore hcomplete
    hu.continuous.measurable ha hreg hlegal hδ hloss
  refine ⟨D, ?_⟩
  simpa only [Measure.map_apply ha MeasurableSet.univ, preimage_univ, measure_univ, mul_one] using htail

end OriginalCore

end OTSelector.Reconstruction

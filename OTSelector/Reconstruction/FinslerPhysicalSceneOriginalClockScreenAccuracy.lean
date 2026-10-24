import OTSelector.Reconstruction.FinslerPhysicalSceneClockScreenOriginal

/-! A fixed clock screen with vanishing original population loss.
The cores vary only as auxiliary restrictions of the same original problem;
no sample or tilt limit is introduced in their construction. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
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

/-- Choose the original coefficient cores with reciprocal root/scalar
losses. Their screens stay below one fixed positive threshold and the sum
of the original population complements tends to zero. -/
theorem exists_original_small_clock_screen_core_sequence_of_face
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
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ D : (m : ℕ) → PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (fun z ↦ ∃ π : Measure (ℝ × ℝ),
        Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) ∧
          ∀ᵐ p ∂π, p.1 ≤ p.2) r
      (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹,
      (∀ m i, (((D m).haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ θ) ∧
      (∀ m, μ (⋃ i, (D m).physicalCoreDomain i)ᶜ ≤
        (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ + (((m + 1 : ℕ) : ℝ≥0∞))⁻¹) ∧
      (∀ m, ν (⋃ i, (D m).physicalCoreDomain i)ᶜ ≤
        (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ + (((m + 1 : ℕ) : ℝ≥0∞))⁻¹) ∧
      Tendsto (fun m ↦ μ (⋃ i, (D m).physicalCoreDomain i)ᶜ +
        ν (⋃ i, (D m).physicalCoreDomain i)ᶜ) atTop (𝓝 0) := by
  classical
  have hexists (m : ℕ) :
      ∃ D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
        (fun z ↦ ∃ π : Measure (ℝ × ℝ),
          Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) ∧
            ∀ᵐ p ∂π, p.1 ≤ p.2) r
        (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹,
        (∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ θ) ∧
        μ (⋃ i, D.physicalCoreDomain i)ᶜ ≤
          (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ + (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ ∧
        ν (⋃ i, D.physicalCoreDomain i)ᶜ ≤
          (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ + (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ :=
    exists_original_small_clock_screen_population_core_of_face hcore hrecovery hF hcomplete
      hu ha hinj hκ hbalance hA hB hμ hν hreg hμreg hface hθ (by simp) (by simp)
  choose D hscreen hμtail hνtail using hexists
  refine ⟨D, hscreen, hμtail, hνtail, ?_⟩
  have htol : Tendsto (fun m : ℕ ↦ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹)
      atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have htotal : Tendsto (fun m : ℕ ↦
      ((((m + 1 : ℕ) : ℝ≥0∞))⁻¹ + (((m + 1 : ℕ) : ℝ≥0∞))⁻¹) +
      ((((m + 1 : ℕ) : ℝ≥0∞))⁻¹ + (((m + 1 : ℕ) : ℝ≥0∞))⁻¹)) atTop (𝓝 0) := by
    simpa only [zero_add] using (htol.add htol).add (htol.add htol)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htotal
    (fun _ ↦ bot_le) (fun m ↦ add_le_add (hμtail m) (hνtail m))

end OriginalCore
end OTSelector.Reconstruction

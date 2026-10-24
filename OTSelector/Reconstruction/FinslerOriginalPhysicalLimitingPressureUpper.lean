import OTSelector.Reconstruction.FinslerRelativeLawOriginalPhysicalPairedExpectedUpper
import OTSelector.Reconstruction.FinslerOriginalWeightPopulationPressureUpper

/-! The actual original calibrated physical data produce the complete expected competitor. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
universe u₁ u₂
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

variable {E : Type u₁} {M : Type u₂} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- Actual original calibrated physical data produce their full limiting
finite-class pressure upper without any empirical, class-law, grid-cover,
cutoff, pressure-limit or sharp-comparison callback. The same original
population, classifier and iid experiment are retained at every step. -/
theorem exists_original_physical_limiting_pressure_upper
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂μ, b (a x,u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y,u y) = y)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (πOriginal : Measure (M × M)) (hπOriginal : Vlasov.IsCoupling πOriginal μ ν)
    (hcalOriginal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂πOriginal, u p.2 - u p.1 = dist p.1 p.2)
    (hδne : δ ≠ 0) (hlossne : loss ≠ 0) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (retentionError splitError : ℝ) (hretention : 0 < retentionError)
    (hretention1 : retentionError < 1) (hsplitError : 0 < splitError)
    (f : M × M →ᵇ ℝ) {ε probeError : ℝ} (hε : 0 < ε) (hprobe : 0 < probeError)
    (hsmall : 3 * ε + 2 * ε ^ 2 < 1) (hq : 4 < Module.finrank ℝ E - 1) :
    ∃ (I : Set ℝ), IsCompact I ∧ ∃ originalGap : ℝ, 0 < originalGap ∧
    ∃ γ : Kernel (ℚ → M) (ℝ × ℝ), IsMarkovKernel γ ∧
    ∃ D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss,
    ∃ (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
      (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M)),
      D.originalWeightLimitingPressureData γ originalGap Q U retentionError splitError f ε probeError := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  letI : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨I,hI,originalGap,hgap,γ,hγ,D,Q,U,hdata⟩ :=
    exists_original_physical_sharp_paired_expected_upper hcore hκ hF hcomplete hu ha hinj horder hb
      hμreg hνreg hμinv hνinv hA hB hAB hμA hνB πOriginal hπOriginal hcalOriginal
      hδne hlossne hδ hδ1 retentionError splitError hretention hretention1 hsplitError
      f hε hprobe hsmall hq
  have hlabels := original_calibrated_coupling_labels μ ν πOriginal πOriginal hπOriginal
    le_rfl a u horder hμreg hνreg hcalOriginal
  have hbalance : ν.map a = μ.map a :=
    (map_label_eq_of_coupling hπOriginal ha ha (hlabels.mono fun _ h ↦ h.1)).symm
  exact ⟨I,hI,originalGap,hgap,γ,hγ,D,Q,U,
    D.originalWeightSharpPairedPopulationData_pressure_upper γ originalGap Q U retentionError splitError
      f ε probeError ha hF hcomplete hu hinj hb hμinv hνinv hbalance hκ (by omega) hdata⟩

end OTSelector.Reconstruction

import OTSelector.Reconstruction.FinslerRelativeLawOriginalSharpExpectedFromCoreLaw

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

/-- One original calibrated coupling and the original Haar core producer give
actual conditional clocks, a full clock range, small screens, class geometry,
one rebuilt original-marginal population and the full expected assignment bound.
No clock coupling, pressure core, class geometry or empirical callback is assumed. -/
theorem exists_original_physical_sharp_expected_upper
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
      D.originalWeightSharpPopulationData γ originalGap Q U retentionError splitError f ε probeError ha := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  letI : BorelSpace (ℚ → M) := inferInstance
  have hum : Measurable u := hu.continuous.measurable
  obtain ⟨gap,hgap,hsep⟩ := exists_original_support_gap hA hB hAB
  let I := (u '' A) ∪ (u '' B)
  have hI : IsCompact I := (hA.image hu.continuous).union (hB.image hu.continuous)
  have hμI : ∀ᵐ x ∂μ, u x ∈ I := hμA.mono fun x hx ↦ Or.inl (mem_image_of_mem u hx)
  have hνI : ∀ᵐ y ∂ν, u y ∈ I := hνB.mono fun y hy ↦ Or.inr (mem_image_of_mem u hy)
  have hlabels := original_calibrated_coupling_labels μ ν πOriginal πOriginal
    hπOriginal le_rfl a u horder hμreg hνreg hcalOriginal
  have hπA : ∀ᵐ p ∂πOriginal, p.1 ∈ A :=
    ae_of_ae_map measurable_fst.aemeasurable (hπOriginal.1.symm ▸ hμA)
  have hπB : ∀ᵐ p ∂πOriginal, p.2 ∈ B :=
    ae_of_ae_map measurable_snd.aemeasurable (hπOriginal.2.symm ▸ hνB)
  have hgapClock : ∀ᵐ p ∂πOriginal, gap ≤ u p.2 - u p.1 := by
    filter_upwards [hπA,hπB,hcalOriginal] with p hpA hpB hpCal
    rw [hpCal]
    exact hsep p.1 hpA p.2 hpB
  obtain ⟨γ,hγ,hGood⟩ := exists_original_clockPair_kernel_with_range μ ν πOriginal
    hπOriginal a u ha hum (hlabels.mono fun _ h ↦ h.1) gap hgapClock I hI.measurableSet hμI hνI
  letI : IsMarkovKernel γ := hγ
  obtain ⟨D,Q,U,hdata⟩ := exists_original_clockClass_sharp_expected_upper γ gap hcore hGood hκ
    hF hcomplete hu ha hinj horder hb hμreg hνreg hμinv hνinv hA hB hAB hμA hνB
    πOriginal hπOriginal hcalOriginal hI hgap hδne hlossne hδ hδ1
    retentionError splitError hretention hretention1 hsplitError f hε hprobe hsmall hq
  exact ⟨I,hI,gap,hgap,γ,hγ,D,Q,U,hdata⟩

end OTSelector.Reconstruction

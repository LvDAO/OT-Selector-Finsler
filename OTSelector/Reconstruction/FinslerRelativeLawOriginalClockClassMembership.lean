import OTSelector.Reconstruction.FinslerRelativeLawCoreClockPair
import OTSelector.Reconstruction.FinslerRelativeLawActualCorePointSampling
import OTSelector.Reconstruction.FiniteScalarBins

/-! The original full conditional clock range discharges actual bin membership. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- An exact finite-bin classifier reads every scalar in the original range
in its literal bin, independently of the enumeration order. -/
theorem FiniteScalarBins.mem_classified_cell {I : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins I width) (classify : ℝ → Fin Q.count)
    (hclass : ∀ j s, s ∈ Q.cell j → classify s = j) {s : ℝ} (hs : s ∈ I) :
    s ∈ Q.cell (classify s) := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp (Q.union_eq.symm ▸ hs)
  rw [hclass j s hj]
  exact hj

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)} [IsFiniteMeasure lambda]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

omit [BorelSpace E] [IsFiniteMeasure lambda] in
/-- Original conditional clock support on an actual core yields the literal
original physical clock range there. This one event precedes every finite-bin
reference, classifier and sample-dependent retained optimizer. -/
theorem PopulationLocalPressureCore.original_clock_range_on_core_ae
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) (gap : ℝ) (I : Set ℝ)
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (hI : MeasurableSet I)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    (i : Fin D.haar.continuous.count) :
    (∀ᵐ x ∂μ, a x ∈ (D.haar.continuous.coefficient i).roots → u x ∈ I) ∧
    (∀ᵐ y ∂ν, a y ∈ (D.haar.continuous.coefficient i).roots → u y ∈ I) := by
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  have hC : MeasurableSet C.roots := C.roots_compact.measurableSet
  have hgood z (hz : z ∈ C.roots) : originalClockPairGood γ
      (condDistrib u a μ) (condDistrib u a ν) gap I z := by
    exact (D.haar.continuous.population.good z
      (D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i, hz⟩)).1
  have hs : ∀ᵐ p ∂lambda.restrict C.roots ⊗ₘ condDistrib u a μ, p.2 ∈ I := by
    have hfields : ∀ᵐ z ∂lambda.restrict C.roots, ∀ᵐ s ∂condDistrib u a μ z, s ∈ I :=
      (ae_restrict_mem hC).mono fun z hz ↦ (hgood z hz).2.2.1
    exact Measure.ae_compProd_of_ae_ae (measurable_snd hI) hfields
  have ht : ∀ᵐ p ∂lambda.restrict C.roots ⊗ₘ condDistrib u a ν, p.2 ∈ I := by
    have hfields : ∀ᵐ z ∂lambda.restrict C.roots, ∀ᵐ t ∂condDistrib u a ν z, t ∈ I :=
      (ae_restrict_mem hC).mono fun z hz ↦ (hgood z hz).2.2.2
    exact Measure.ae_compProd_of_ae_ae (measurable_snd hI) hfields
  have hsource := original_label_clock_restrict_eq_compProd μ ha hu hC
  have htarget := original_label_clock_restrict_eq_compProd ν ha hu hC
  rw [hlabel0] at hsource
  rw [hlabel1] at htarget
  rw [← hsource] at hs
  rw [← htarget] at ht
  exact ⟨ae_imp_of_ae_restrict (ae_of_ae_map (ha.prodMk hu).aemeasurable hs),
    ae_imp_of_ae_restrict (ae_of_ae_map (ha.prodMk hu).aemeasurable ht)⟩

omit [BorelSpace E] [IsFiniteMeasure lambda] in
/-- The original core clock-range event holds on all original marked indices
before selecting any retained cells or optimizers. It therefore applies
simultaneously to every later reference's bins and exact classifier. -/
theorem PopulationLocalPressureCore.original_marked_iid_core_clock_range_ae
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) (gap : ℝ) (I : Set ℝ)
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (hI : MeasurableSet I) (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    (i : Fin D.haar.continuous.count)
    {πWhole : Measure (M × M)} [IsFiniteMeasure πWhole]
    (hπWhole : Vlasov.IsCoupling πWhole μ ν)
    {T : Type*} [Fintype T] [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    (Types : PopulationSubcouplingTypes πWhole T)
    {NS NT : Type*} [Fintype NS] [Fintype NT] :
    ∀ᵐ sample ∂(Measure.pi (fun _ : NS ↦ Types.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : NT ↦ Types.targetMarkedLaw ν)),
      (∀ j, a (sample.1 j).1 ∈ (D.haar.continuous.coefficient i).roots → u (sample.1 j).1 ∈ I) ∧
      (∀ k, a (sample.2 k).1 ∈ (D.haar.continuous.coefficient i).roots → u (sample.2 k).1 ∈ I) := by
  obtain ⟨hs, ht⟩ := D.original_clock_range_on_core_ae γ gap I hI hcomplete ha hu hlabel0 hlabel1 i
  have hsource : ∀ᵐ x ∂Measure.pi (fun _ : NS ↦ μ),
      ∀ j, a (x j) ∈ (D.haar.continuous.coefficient i).roots → u (x j) ∈ I :=
    ae_all_iff.mpr fun j ↦ (Measure.quasiMeasurePreserving_eval (fun _ : NS ↦ μ) j).ae hs
  have htarget : ∀ᵐ y ∂Measure.pi (fun _ : NT ↦ ν),
      ∀ k, a (y k) ∈ (D.haar.continuous.coefficient i).roots → u (y k) ∈ I :=
    ae_all_iff.mpr fun k ↦ (Measure.quasiMeasurePreserving_eval (fun _ : NT ↦ ν) k).ae ht
  apply Types.iid_original_physical_property (I := NS) (J := NT) hπWhole
    (fun sample : (NS → M) × (NT → M) ↦
      (∀ j, a (sample.1 j) ∈ (D.haar.continuous.coefficient i).roots → u (sample.1 j) ∈ I) ∧
      (∀ k, a (sample.2 k) ∈ (D.haar.continuous.coefficient i).roots → u (sample.2 k) ∈ I))
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsource,
    Measure.quasiMeasurePreserving_snd.ae htarget] with sample hs ht
  exact ⟨hs, ht⟩

end OTSelector.Reconstruction

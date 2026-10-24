import OTSelector.Transport.Coupling.PopulationClassFlow

/-!
Original reference-bin feasibility and measurable legal population reconstruction.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A single actual conditional clock-pair law proves finite feasibility for
any reference's bins covering the unchanged original clocks. The bins need not
be fixed before the full-measure conditional pair statement. -/
theorem actualClockClassFlow_original_feasible_at
    {I J : Type*} [Fintype I] [Fintype J]
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ]
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hγ : Vlasov.IsCoupling γ μ ν)
    (S : I → Set ℝ) (T : J → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (Disjoint on S)) (hdT : Pairwise (Disjoint on T))
    (hcoverS : ∀ᵐ s ∂μ, s ∈ ⋃ i, S i) (hcoverT : ∀ᵐ t ∂ν, t ∈ ⋃ j, T j)
    (allowed : I → J → Prop) (legal : ℝ × ℝ → Prop)
    (hlegal : ∀ᵐ p ∂γ, legal p)
    (hbins : ∀ i j, ∀ s ∈ S i, ∀ t ∈ T j, legal (s, t) → allowed i j) :
    (∀ i j, 0 ≤ actualClockClassFlow γ S T i j) ∧
    (∀ i, ∑ j, actualClockClassFlow γ S T i j = μ.real (S i)) ∧
    (∀ j, ∑ i, actualClockClassFlow γ S T i j = ν.real (T j)) ∧
    (∀ i j, ¬ allowed i j → actualClockClassFlow γ S T i j = 0) ∧
    (∑ i, ∑ j, actualClockClassFlow γ S T i j) = 1 := by
  have hsγ : ∀ᵐ p ∂γ, p.1 ∈ ⋃ i, S i :=
    ae_of_ae_map measurable_fst.aemeasurable (hγ.1.symm ▸ hcoverS)
  have htγ : ∀ᵐ p ∂γ, p.2 ∈ ⋃ j, T j :=
    ae_of_ae_map measurable_snd.aemeasurable (hγ.2.symm ▸ hcoverT)
  have hrow (i : I) : (∑ j, actualClockClassFlow γ S T i j) = μ.real (S i) := by
    rw [actualClockClassFlow_row γ S T hS hT hdT htγ i, hγ.1]
  refine ⟨actualClockClassFlow_nonneg _ _ _, hrow, ?_, ?_, ?_⟩
  · intro j
    rw [actualClockClassFlow_col γ S T hS hT hdS hsγ j, hγ.2]
  · exact actualClockClassFlow_zero γ S T allowed legal hlegal
      (fun i j p hi hj hp ↦ hbins i j p.1 hi p.2 hj hp)
  · simp_rw [hrow]
    rw [← measureReal_iUnion_fintype hdS hS]
    have he : μ.real (⋃ i, S i) = μ.real univ := by
      apply measureReal_congr
      filter_upwards [hcoverS] with s hs
      apply propext
      change (s ∈ ⋃ i, S i) ↔ s ∈ (univ : Set ℝ)
      exact iff_of_true hs (mem_univ s)
    rw [he]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one]

/-- The original full-measure pair condition can be chosen before all reference
bins, so every later local finite Hall test comes from the same original law. -/
theorem exists_original_clockPair_universal_classFlow
    {X Z : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Z]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure (X × X)) (hπ : Vlasov.IsCoupling π μ ν)
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (hlabel : ∀ᵐ p ∂π, a p.1 = a p.2)
    (δ : ℝ) (hgap : ∀ᵐ p ∂π, δ ≤ u p.2 - u p.1) :
    ∃ γ : Kernel Z (ℝ × ℝ), IsMarkovKernel γ ∧
      ∀ᵐ z ∂μ.map a,
        ∀ (m n : ℕ) (S : Fin m → Set ℝ) (T : Fin n → Set ℝ),
          (∀ i, MeasurableSet (S i)) → (∀ j, MeasurableSet (T j)) →
          Pairwise (Disjoint on S) → Pairwise (Disjoint on T) →
          (∀ᵐ s ∂condDistrib u a μ z, s ∈ ⋃ i, S i) →
          (∀ᵐ t ∂condDistrib u a ν z, t ∈ ⋃ j, T j) →
          ∀ (allowed : Fin m → Fin n → Prop),
            (∀ i j, ∀ s ∈ S i, ∀ t ∈ T j, δ ≤ t - s → allowed i j) →
            (∀ i j, 0 ≤ actualClockClassFlow (γ z) S T i j) ∧
            (∀ i, ∑ j, actualClockClassFlow (γ z) S T i j = (condDistrib u a μ z).real (S i)) ∧
            (∀ j, ∑ i, actualClockClassFlow (γ z) S T i j = (condDistrib u a ν z).real (T j)) ∧
            (∀ i j, ¬ allowed i j → actualClockClassFlow (γ z) S T i j = 0) ∧
            (∑ i, ∑ j, actualClockClassFlow (γ z) S T i j) = 1 := by
  obtain ⟨γ, hγ, _, _, _, hactual⟩ := exists_original_clockPair_kernel μ ν π hπ a u ha hu hlabel δ hgap
  let _instPairMarkov : IsMarkovKernel γ := hγ
  refine ⟨γ, hγ, hactual.mono ?_⟩
  intro z hz m n S T hS hT hdS hdT hs ht allowed hbins
  exact actualClockClassFlow_original_feasible_at (γ z) (condDistrib u a μ z) (condDistrib u a ν z)
    hz.1 S T hS hT hdS hdT hs ht allowed (fun p ↦ δ ≤ p.2 - p.1) hz.2 hbins

/-- The original physical clock range passes to both literal original
conditional laws, together with the same original pair kernel. This single
full-measure condition precedes every later finite reference-bin choice. -/
theorem exists_original_clockPair_kernel_with_range
    {X Z : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Z]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure (X × X)) (hπ : Vlasov.IsCoupling π μ ν)
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (hlabel : ∀ᵐ p ∂π, a p.1 = a p.2)
    (gap : ℝ) (hgap : ∀ᵐ p ∂π, gap ≤ u p.2 - u p.1)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hμI : ∀ᵐ x ∂μ, u x ∈ I) (hνI : ∀ᵐ y ∂ν, u y ∈ I) :
    ∃ γ : Kernel Z (ℝ × ℝ), IsMarkovKernel γ ∧
      ∀ᵐ z ∂μ.map a,
        Vlasov.IsCoupling (γ z) (condDistrib u a μ z) (condDistrib u a ν z) ∧
        (∀ᵐ p ∂γ z, gap ≤ p.2 - p.1) ∧
        (∀ᵐ s ∂condDistrib u a μ z, s ∈ I) ∧
        (∀ᵐ t ∂condDistrib u a ν z, t ∈ I) := by
  obtain ⟨γ, hγ, _, hsource, htarget, hactual⟩ :=
    exists_original_clockPair_kernel μ ν π hπ a u ha hu hlabel gap hgap
  let _instLabelProbability : IsProbabilityMeasure (μ.map a) := Measure.isProbabilityMeasure_map ha.aemeasurable
  have hs : ∀ᵐ z ∂μ.map a, ∀ᵐ s ∂condDistrib u a μ z, s ∈ I := by
    apply Measure.ae_ae_of_ae_compProd (p := fun p : Z × ℝ ↦ p.2 ∈ I)
    rw [hsource]
    exact (ae_map_iff (ha.prodMk hu).aemeasurable (measurable_snd hI)).mpr hμI
  have ht : ∀ᵐ z ∂μ.map a, ∀ᵐ t ∂condDistrib u a ν z, t ∈ I := by
    apply Measure.ae_ae_of_ae_compProd (p := fun p : Z × ℝ ↦ p.2 ∈ I)
    rw [htarget]
    exact (ae_map_iff (ha.prodMk hu).aemeasurable (measurable_snd hI)).mpr hνI
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hactual, hs, ht] with z hz hs ht
  exact ⟨hz.1, hz.2, hs, ht⟩

end OTSelector.Reconstruction

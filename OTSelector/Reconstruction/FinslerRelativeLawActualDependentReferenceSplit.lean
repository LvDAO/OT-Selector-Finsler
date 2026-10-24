import OTSelector.Reconstruction.FinslerConcreteUpperClassReference
import OTSelector.Finite.NormalizedReferenceHallSplit
import OTSelector.Transport.Coupling.MeasurableReferenceFlow
import OTSelector.Reconstruction.FinslerRelativeLawCoreClockPair

/-!
Original reference-bin feasibility and measurable legal population reconstruction.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- Original finite-bin continuity selects actual disjoint cells carrying an
explicit legal reference split. Each reference fixes its own bins, Hall
accuracy and geometry neighborhood before finite selection. -/
theorem PopulationLocalPressureCore.exists_dependent_original_classSplit_cells
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (i : Fin D.haar.continuous.count)
    (m n : (D.haar.continuous.coefficient i).roots → ℕ)
    (S : ∀ ref, Fin (m ref) → Set ℝ) (T : ∀ ref, Fin (n ref) → Set ℝ)
    (hS : ∀ ref j, MeasurableSet (S ref j)) (hT : ∀ ref k, MeasurableSet (T ref k))
    (allowed : ∀ ref, Fin (m ref) → Fin (n ref) → Prop)
    (horder : ∀ ref j j' k k', j ≤ j' → k' ≤ k → allowed ref j' k' → allowed ref j k)
    (V : (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (hVopen : ∀ ref, IsOpen (V ref)) (hVself : ∀ ref, ref.val ∈ V ref)
    (A : ∀ ref, (ℚ → M) → Fin (m ref) → Fin (n ref) → ℝ)
    (hA : ∀ ref, ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ V ref,
      (∀ j k, 0 ≤ A ref z j k) ∧
      (∀ j, ∑ k, A ref z j k = (populationTwoColorClockKernel u a η₀ η₁ 0 z).real (S ref j)) ∧
      (∀ k, ∑ j, A ref z j k = (populationTwoColorClockKernel u a η₀ η₁ 1 z).real (T ref k)) ∧
      (∀ j k, ¬ allowed ref j k → A ref z j k = 0) ∧ (∑ j, ∑ k, A ref z j k) = 1)
    (η ε : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε) :
    ∃ (N : ℕ) (reference : Fin N → (D.haar.continuous.coefficient i).roots)
      (cell : Fin N → Set (ℚ → M)),
      (∀ c, MeasurableSet (cell c)) ∧ Pairwise (Disjoint on cell) ∧
      (⋃ c, cell c) = (D.haar.continuous.coefficient i).roots ∧
      ∀ c, cell c ⊆ (D.haar.continuous.coefficient i).roots ∩ V (reference c) ∧
        ∀ z ∈ cell c,
          let ref := reference c
          let d := D.rootIntensity i z
          let d₀ := D.rootIntensity i ref.val
          let Q := referenceResidualClockFlow
            (fun j ↦ D.rootWeightedClockBinMass i 0 (S ref j) ref.val)
            (fun k ↦ D.rootWeightedClockBinMass i 1 (T ref k) ref.val) η
            (fun j ↦ D.rootWeightedClockBinMass i 0 (S ref j) z)
            (fun k ↦ D.rootWeightedClockBinMass i 1 (T ref k) z)
          (∀ j k, 0 ≤ (1 - η) * (d₀ * A ref ref.val j k) / d) ∧
          (∀ j k, 0 ≤ Q j k / d) ∧
          (∀ j, ∑ k, ((1 - η) * (d₀ * A ref ref.val j k) / d + Q j k / d) =
            (populationTwoColorClockKernel u a η₀ η₁ 0 z).real (S ref j)) ∧
          (∀ k, ∑ j, ((1 - η) * (d₀ * A ref ref.val j k) / d + Q j k / d) =
            (populationTwoColorClockKernel u a η₀ η₁ 1 z).real (T ref k)) ∧
          (∀ j k, ¬ allowed ref j k →
            (1 - η) * (d₀ * A ref ref.val j k) / d = 0 ∧ Q j k / d = 0) ∧
          (∑ j, ∑ k, Q j k / d) ≤ η + ε := by
  classical
  let K := (D.haar.continuous.coefficient i).roots
  let d := D.rootIntensity i
  let asrc := fun ref z j ↦ (populationTwoColorClockKernel u a η₀ η₁ 0 z).real (S ref j)
  let btgt := fun ref z k ↦ (populationTwoColorClockKernel u a η₀ η₁ 1 z).real (T ref k)
  have hd (z) (hz : z ∈ K) : 0 < d z := by
    let I := D.haar.intensity i
    have hzI : z ∈ I.roots := (D.haar.intensity_roots i).symm ▸ hz
    exact I.lower_pos.trans_le (I.bounds _ (mem_image_of_mem _ hzI)).1
  have hlocal (ref : K) : ∃ τ : ℝ, 0 < τ ∧
      ∀ (d' ε' : ℝ) (a' : Fin (m ref) → ℝ) (b' : Fin (n ref) → ℝ)
        (A' : Fin (m ref) → Fin (n ref) → ℝ),
        0 < d' → 0 ≤ ε' → d' ≤ (1 + ε') * d ref.val →
        (∀ j k, 0 ≤ A' j k) → (∀ j, ∑ k, A' j k = a' j) → (∀ k, ∑ j, A' j k = b' k) →
        (∀ j k, ¬ allowed ref j k → A' j k = 0) → (∑ j, a' j = 1) →
        (∀ j, |d' * a' j - d ref.val * asrc ref ref.val j| ≤ τ) →
        (∀ k, |d' * b' k - d ref.val * btgt ref ref.val k| ≤ τ) →
        let Q := referenceResidualClockFlow (fun j ↦ d ref.val * asrc ref ref.val j)
          (fun k ↦ d ref.val * btgt ref ref.val k) η (fun j ↦ d' * a' j) (fun k ↦ d' * b' k)
        (∀ j k, 0 ≤ (1 - η) * (d ref.val * A ref ref.val j k) / d') ∧
        (∀ j k, 0 ≤ Q j k / d') ∧
        (∀ j, ∑ k, ((1 - η) * (d ref.val * A ref ref.val j k) / d' + Q j k / d') = a' j) ∧
        (∀ k, ∑ j, ((1 - η) * (d ref.val * A ref ref.val j k) / d' + Q j k / d') = b' k) ∧
        (∀ j k, ¬ allowed ref j k →
          (1 - η) * (d ref.val * A ref ref.val j k) / d' = 0 ∧ Q j k / d' = 0) ∧
        (∑ j, ∑ k, Q j k / d') ≤ η + ε' := by
    obtain ⟨hp, hr, hc, hz, ht⟩ := hA ref ref.val ⟨ref.property, hVself ref⟩
    apply exists_tolerance_normalized_reference_classSplit (allowed ref) (horder ref)
      (fun j ↦ d ref.val * asrc ref ref.val j) (fun k ↦ d ref.val * btgt ref ref.val k)
      (fun j k ↦ d ref.val * A ref ref.val j k)
      (fun j k ↦ mul_nonneg (hd ref.val ref.property).le (hp j k))
    · intro j
      rw [← Finset.mul_sum, hr j]
    · intro k
      rw [← Finset.mul_sum, hc k]
    · intro j k hnot
      rw [hz j k hnot, mul_zero]
    · exact hd ref.val ref.property
    · rw [← Finset.mul_sum]
      change d ref.val * (∑ j, asrc ref ref.val j) = d ref.val
      dsimp only [asrc]
      simp_rw [← hr]
      rw [ht, mul_one]
    · exact hη
    · exact hη1
  choose τ hτ hsplit using hlocal
  let B := fun ref : K ↦ fun c : Fin (m ref) ⊕ Fin (n ref) ↦
    match c with | .inl j => S ref j | .inr k => T ref k
  have hB (ref : K) (c) : MeasurableSet (B ref c) := by
    cases c with | inl j => exact hS ref j | inr k => exact hT ref k
  obtain ⟨N, reference, cell, hcell, hdisj, hunion, hclose⟩ :=
    D.exists_finite_dependent_clockClass_cells hcomplete i (fun ref ↦ Fin (m ref) ⊕ Fin (n ref))
      B hB τ hτ hε V hVopen hVself
  refine ⟨N, reference, cell, hcell, hdisj, hunion, fun c ↦ ⟨(hclose c).1, ?_⟩⟩
  intro z hz
  let ref := reference c
  have hzK : z ∈ K := ((hclose c).1 hz).1
  have hdupper : d z ≤ (1 + ε) * d ref.val := by
    have he := ((hclose c).2 z hz).1.le
    have hu := (abs_le.mp he).2
    nlinarith
  obtain ⟨hp, hr, hc, hzero, ht⟩ := hA ref z ((hclose c).1 hz)
  have htotal : ∑ j, asrc ref z j = 1 := by
    dsimp only [asrc]
    simp_rw [← hr]
    exact ht
  apply hsplit ref (d z) ε (asrc ref z) (btgt ref z) (A ref z)
    (hd z hzK) hε.le hdupper hp hr hc hzero htotal
  · intro j
    exact (((hclose c).2 z hz).2 0 (.inl j)).le
  · intro k
    exact (((hclose c).2 z hz).2 1 (.inr k)).le

/-- The actual reference split extends measurably off the retained original
core, without changing any intensity or finite flow on its cells. -/
theorem PopulationLocalPressureCore.exists_measurable_dependent_original_classSplit_cells
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (i : Fin D.haar.continuous.count)
    (m n : (D.haar.continuous.coefficient i).roots → ℕ)
    (S : ∀ ref, Fin (m ref) → Set ℝ) (T : ∀ ref, Fin (n ref) → Set ℝ)
    (hS : ∀ ref j, MeasurableSet (S ref j)) (hT : ∀ ref k, MeasurableSet (T ref k))
    (allowed : ∀ ref, Fin (m ref) → Fin (n ref) → Prop)
    (horder : ∀ ref j j' k k', j ≤ j' → k' ≤ k → allowed ref j' k' → allowed ref j k)
    (V : (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (hVopen : ∀ ref, IsOpen (V ref)) (hVself : ∀ ref, ref.val ∈ V ref)
    (A : ∀ ref, (ℚ → M) → Fin (m ref) → Fin (n ref) → ℝ)
    (hA : ∀ ref, ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ V ref,
      (∀ j k, 0 ≤ A ref z j k) ∧
      (∀ j, ∑ k, A ref z j k = (populationTwoColorClockKernel u a η₀ η₁ 0 z).real (S ref j)) ∧
      (∀ k, ∑ j, A ref z j k = (populationTwoColorClockKernel u a η₀ η₁ 1 z).real (T ref k)) ∧
      (∀ j k, ¬ allowed ref j k → A ref z j k = 0) ∧ (∑ j, ∑ k, A ref z j k) = 1)
    (η ε : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε) :
    ∃ (N : ℕ) (reference : Fin N → (D.haar.continuous.coefficient i).roots)
      (cell : Fin N → Set (ℚ → M))
      (Pf Qf : ∀ c : Fin N, (ℚ → M) → Fin (m (reference c)) → Fin (n (reference c)) → ℝ),
      (∀ c, MeasurableSet (cell c)) ∧ Pairwise (Disjoint on cell) ∧
      (⋃ c, cell c) = (D.haar.continuous.coefficient i).roots ∧
      (∀ c, cell c ⊆ (D.haar.continuous.coefficient i).roots ∩ V (reference c)) ∧
      (∀ c j k, Measurable (fun z ↦ Pf c z j k)) ∧
      (∀ c j k, Measurable (fun z ↦ Qf c z j k)) ∧
      ∀ c, ∀ z ∈ cell c,
        (∀ j k, 0 ≤ Pf c z j k) ∧ (∀ j k, 0 ≤ Qf c z j k) ∧
        (∀ j, ∑ k, (Pf c z j k + Qf c z j k) =
          (populationTwoColorClockKernel u a η₀ η₁ 0 z).real (S (reference c) j)) ∧
        (∀ k, ∑ j, (Pf c z j k + Qf c z j k) =
          (populationTwoColorClockKernel u a η₀ η₁ 1 z).real (T (reference c) k)) ∧
        (∀ j k, ¬ allowed (reference c) j k → Pf c z j k = 0 ∧ Qf c z j k = 0) ∧
        (∑ j, ∑ k, Qf c z j k) ≤ η + ε ∧
        ∀ j k, Pf c z j k = (1 - η) *
          (D.rootIntensity i (reference c).val * A (reference c) (reference c).val j k) /
            D.rootIntensity i z := by
  classical
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let K := (D.haar.continuous.coefficient i).roots
  let d := D.rootIntensity i
  have hK : MeasurableSet K := (D.haar.continuous.coefficient i).roots_compact.measurableSet
  have hdc : ContinuousOn d K := by
    have he : D.rootWeightedClockBinMass i 0 univ = d := by
      funext z
      simp only [PopulationLocalPressureCore.rootWeightedClockBinMass, measureReal_def,
        measure_univ, ENNReal.toReal_one, mul_one]
      rfl
    rw [← he]
    exact D.continuousOn_rootWeightedClockBinMass i 0 MeasurableSet.univ
  let de := coreIntensityExtension K d
  have hmde : Measurable de := measurable_coreIntensityExtension K hK d hdc
  obtain ⟨N, reference, cell, hcell, hdisj, hunion, hsplit⟩ :=
    D.exists_dependent_original_classSplit_cells hcomplete i m n S T hS hT allowed horder
      V hVopen hVself A hA η ε hη hη1 hε
  let asrc := fun c z j ↦ (populationTwoColorClockKernel u a η₀ η₁ 0 z).real (S (reference c) j)
  let btgt := fun c z k ↦ (populationTwoColorClockKernel u a η₀ η₁ 1 z).real (T (reference c) k)
  let Pf := fun c z j k ↦ (1 - η) *
    (d (reference c).val * A (reference c) (reference c).val j k) / de z
  let Qf := fun c z j k ↦ referenceResidualClockFlow
    (fun j ↦ d (reference c).val * asrc c (reference c).val j)
    (fun k ↦ d (reference c).val * btgt c (reference c).val k) η
    (fun j ↦ de z * asrc c z j) (fun k ↦ de z * btgt c z k) j k / de z
  have hma (c j) : Measurable (fun z ↦ asrc c z j) :=
    ((populationTwoColorClockKernel u a η₀ η₁ 0).measurable_coe (hS (reference c) j)).ennreal_toReal
  have hmb (c k) : Measurable (fun z ↦ btgt c z k) :=
    ((populationTwoColorClockKernel u a η₀ η₁ 1).measurable_coe (hT (reference c) k)).ennreal_toReal
  have hmPf (c j k) : Measurable (fun z ↦ Pf c z j k) :=
    measurable_div.comp (measurable_const.prodMk hmde)
  have hmQf (c j k) : Measurable (fun z ↦ Qf c z j k) :=
    measurable_div.comp ((measurable_referenceResidualClockFlow _ _ η _ _
      (fun j ↦ measurable_mul.comp (hmde.prodMk (hma c j)))
      (fun k ↦ measurable_mul.comp (hmde.prodMk (hmb c k))) j k).prodMk hmde)
  refine ⟨N, reference, cell, Pf, Qf, hcell, hdisj, hunion,
    fun c ↦ (hsplit c).1, hmPf, hmQf, ?_⟩
  intro c z hz
  have hzK : z ∈ K := ((hsplit c).1 hz).1
  have he : de z = d z := coreIntensityExtension_eq K d hzK
  have h := (hsplit c).2 z hz
  change (∀ j k, 0 ≤ Pf c z j k) ∧ (∀ j k, 0 ≤ Qf c z j k) ∧ _
  have hsplit' :
      (∀ j k, 0 ≤ Pf c z j k) ∧ (∀ j k, 0 ≤ Qf c z j k) ∧
      (∀ j, ∑ k, (Pf c z j k + Qf c z j k) = asrc c z j) ∧
      (∀ k, ∑ j, (Pf c z j k + Qf c z j k) = btgt c z k) ∧
      (∀ j k, ¬ allowed (reference c) j k → Pf c z j k = 0 ∧ Qf c z j k = 0) ∧
      (∑ j, ∑ k, Qf c z j k) ≤ η + ε := by
    simpa only [Pf, Qf, he, asrc, btgt,
      PopulationLocalPressureCore.rootWeightedClockBinMass] using h
  exact ⟨hsplit'.1, hsplit'.2.1, hsplit'.2.2.1, hsplit'.2.2.2.1,
    hsplit'.2.2.2.2.1, hsplit'.2.2.2.2.2, fun j k ↦ by simp only [Pf, he]; rfl⟩

/-- One actual original conditional pair kernel retained by the original core
supplies every reference matrix. Full original clock-range bin coverage
therefore discharges all finite feasibility assumptions before cell selection. -/
theorem PopulationLocalPressureCore.exists_measurable_actual_reference_classSplit_cells
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ) (I : Set ℝ)
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a η₀) (condDistrib u a η₁) gap I) r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (i : Fin D.haar.continuous.count)
    (m n : (D.haar.continuous.coefficient i).roots → ℕ)
    (S : ∀ ref, Fin (m ref) → Set ℝ) (T : ∀ ref, Fin (n ref) → Set ℝ)
    (hS : ∀ ref j, MeasurableSet (S ref j)) (hT : ∀ ref k, MeasurableSet (T ref k))
    (allowed : ∀ ref, Fin (m ref) → Fin (n ref) → Prop)
    (horder : ∀ ref j j' k k', j ≤ j' → k' ≤ k → allowed ref j' k' → allowed ref j k)
    (V : (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (hVopen : ∀ ref, IsOpen (V ref)) (hVself : ∀ ref, ref.val ∈ V ref)
    (hdS : ∀ ref, Pairwise (Disjoint on S ref))
    (hdT : ∀ ref, Pairwise (Disjoint on T ref))
    (hcoverS : ∀ ref, I ⊆ ⋃ j, S ref j) (hcoverT : ∀ ref, I ⊆ ⋃ k, T ref k)
    (hbins : ∀ ref j k, ∀ s ∈ S ref j, ∀ t ∈ T ref k, gap ≤ t - s → allowed ref j k)
    (η ε : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε) :
    ∃ (N : ℕ) (reference : Fin N → (D.haar.continuous.coefficient i).roots)
      (cell : Fin N → Set (ℚ → M))
      (Pf Qf : ∀ c : Fin N, (ℚ → M) → Fin (m (reference c)) → Fin (n (reference c)) → ℝ),
      (∀ c, MeasurableSet (cell c)) ∧ Pairwise (Disjoint on cell) ∧
      (⋃ c, cell c) = (D.haar.continuous.coefficient i).roots ∧
      (∀ c, cell c ⊆ (D.haar.continuous.coefficient i).roots ∩ V (reference c)) ∧
      (∀ c j k, Measurable (fun z ↦ Pf c z j k)) ∧
      (∀ c j k, Measurable (fun z ↦ Qf c z j k)) ∧
      ∀ c, ∀ z ∈ cell c,
        (∀ j k, 0 ≤ Pf c z j k) ∧ (∀ j k, 0 ≤ Qf c z j k) ∧
        (∀ j, ∑ k, (Pf c z j k + Qf c z j k) =
          (populationTwoColorClockKernel u a η₀ η₁ 0 z).real (S (reference c) j)) ∧
        (∀ k, ∑ j, (Pf c z j k + Qf c z j k) =
          (populationTwoColorClockKernel u a η₀ η₁ 1 z).real (T (reference c) k)) ∧
        (∀ j k, ¬ allowed (reference c) j k → Pf c z j k = 0 ∧ Qf c z j k = 0) ∧
        (∑ j, ∑ k, Qf c z j k) ≤ η + ε ∧
        ∀ j k, Pf c z j k = (1 - η) *
          (D.rootIntensity i (reference c).val * actualClockClassFlow (γ (reference c).val) (S (reference c)) (T (reference c)) j k) /
            D.rootIntensity i z := by
  let A := fun ref z ↦ actualClockClassFlow (γ z) (S ref) (T ref)
  apply D.exists_measurable_dependent_original_classSplit_cells hcomplete i m n S T hS hT
    allowed horder V hVopen hVself A ?_ η ε hη hη1 hε
  intro ref z hz
  have hzpop : z ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i, hz.1⟩
  have hg := (D.haar.continuous.population.good z hzpop).1
  exact actualClockClassFlow_original_feasible_at (γ z)
    (condDistrib u a η₀ z) (condDistrib u a η₁ z) hg.1
    (S ref) (T ref) (hS ref) (hT ref) (hdS ref) (hdT ref)
    (hg.2.2.1.mono (fun s hs ↦ hcoverS ref hs))
    (hg.2.2.2.mono (fun t ht ↦ hcoverT ref ht))
    (allowed ref) (fun p ↦ gap ≤ p.2 - p.1) hg.2.1 (hbins ref)

end OTSelector.Reconstruction

import OTSelector.Reconstruction.FinslerRelativeLawWindowReferenceWeightPopulation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPhysicalCellObservation
import OTSelector.Reconstruction.FinslerConcreteUpperActualClassObservation

/-! Actual original population construction with exact retained physical Haar/class laws. -/

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
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b₀ : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- Actual original full clock bins produce a calibrated population whose
retained physical observations have the literal Haar × fixed-class laws on
every selected original cell. The conditional class residual, bin positivity,
normalization weights, label balance and fixed-inverse recovery are derived
inside the same construction, before any empirical selection or residual repair. -/
theorem exists_original_clockClass_observed_sampling_population_with_inverse
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ) (I : Set ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b₀
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (huLip : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {A : Set M} (hA : MeasurableSet A) (ha : Measurable a) (hu : Measurable u)
    (hclockOrder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ A, (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνA : ∀ᵐ y ∂ν, y ∈ A)
    (hb₀ : Measurable b₀)
    (hμinv : ∀ᵐ x ∂μ, b₀ (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b₀ (a y, u y) = y)
    (π : Measure (M × M)) (hπ : Vlasov.IsCoupling π μ ν)
    (hlabel : ∀ᵐ p ∂π, a p.1 = a p.2) (hforward : ∀ᵐ p ∂π, u p.1 ≤ u p.2)
    (hI : IsCompact I) (hgap : 0 < gap)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I gap)
    (V : ∀ i : Fin D.haar.continuous.count, (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (hVopen : ∀ i ref, IsOpen (V i ref)) (hVself : ∀ i ref, ref.val ∈ V i ref)
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (η ε : ℝ) (hη : 0 < η) (hη1 : η < 1) (hε : 0 < ε) :
    ∃ (N : Fin D.haar.continuous.count → ℕ)
      (reference : ∀ i, Fin (N i) → (D.haar.continuous.coefficient i).roots)
      (cell : ∀ i, Fin (N i) → Set (ℚ → M))
      (Pf Qf : ∀ i c, (ℚ → M) → Fin (Q i (reference i c)).count → Fin (Q i (reference i c)).count → ℝ)
      (hcell : ∀ i c, MeasurableSet (cell i c)),
      (∀ i c, cell i c ⊆ (D.haar.continuous.coefficient i).roots ∩ V i (reference i c)) ∧
      (∀ i c j k, Measurable (fun z ↦ Pf i c z j k)) ∧
      (∀ i c j k, Measurable (fun z ↦ Qf i c z j k)) ∧
      (∀ i c z, z ∈ cell i c →
        (∀ j k, 0 ≤ Pf i c z j k) ∧ (∀ j k, 0 ≤ Qf i c z j k) ∧
        (∀ j, ∑ k, (Pf i c z j k + Qf i c z j k) =
          (condDistrib u a μ z).real ((Q i (reference i c)).cell j)) ∧
        (∀ k, ∑ j, (Pf i c z j k + Qf i c z j k) =
          (condDistrib u a ν z).real ((Q i (reference i c)).cell k)) ∧
        (∀ j k, ¬ sSup ((Q i (reference i c)).cell j) + gap / 2 ≤ sInf ((Q i (reference i c)).cell k) →
          Pf i c z j k = 0 ∧ Qf i c z j k = 0) ∧
        (∑ j, ∑ k, Qf i c z j k) ≤ η + ε + δ.toReal) ∧
      (∀ i c,
        let P₀ := D.originalWindowReferenceWeights γ gap I i (reference i c) (Q i (reference i c)) η
        (∀ j k, 0 ≤ P₀ j k) ∧
        (∀ j k, ¬(D.haar.continuous.coefficient i).clockClassAllowed (Q i (reference i c)) j k → P₀ j k = 0) ∧
        (1 - η) * D.rootIntensity i (reference i c).val * (1 - δ.toReal) ≤ (∑ j, ∑ k, P₀ j k) ∧
        0 < ∑ j, ∑ k, P₀ j k) ∧
      (∀ i c z, z ∈ cell i c → ∀ j k, Pf i c z j k =
        D.originalWindowReferenceWeights γ gap I i (reference i c) (Q i (reference i c)) η j k /
          D.rootIntensity i z) ∧
      let C := Sigma (fun i ↦ Fin (N i))
      let cells := fun c : C ↦ cell c.1 c.2
      let hcells := fun c : C ↦ hcell c.1 c.2
      let α := fun (c : C) j ↦ normalizedActualBinKernel (condDistrib u a μ)
        ((Q c.1 (reference c.1 c.2)).cell j) ((Q c.1 (reference c.1 c.2)).measurable_cell j) 0
      let β := fun (c : C) k ↦ normalizedActualBinKernel (condDistrib u a ν)
        ((Q c.1 (reference c.1 c.2)).cell k) ((Q c.1 (reference c.1 c.2)).measurable_cell k) 0
      let KP := fun c : C ↦ finiteClassPopulationKernel (Pf c.1 c.2) (α c) (β c)
      let χ := ((μ.map a) ⊗ₘ finiteCellPairKernel cells hcells KP).map sameLabelPopulationPair
      let _inst : MetricSpace M := F.metricSpace
      Pairwise (Disjoint on cells) ∧
      (⋃ c, cells c) = D.haar.continuous.population.roots ∧
      ∃ Qglobal : Kernel (ℚ → M) (ℝ × ℝ), IsSFiniteKernel Qglobal ∧
      (∀ᵐ z ∂μ.map a, Vlasov.IsCoupling
        (finiteCellPairKernel cells hcells KP z + Qglobal z)
        (condDistrib u a μ z) (condDistrib u a ν z)) ∧
      ∃ ξ : Measure (M × M),
        Vlasov.IsCoupling (χ.map (Prod.map b₀ b₀) + ξ) μ ν ∧
        (∀ᵐ p ∂χ.map (Prod.map b₀ b₀) + ξ, u p.2 - u p.1 = dist p.1 p.2) ∧
        ξ ≤ χ.map (Prod.map b₀ b₀) + ξ ∧
        ξ univ ≤ ENNReal.ofReal (η + ε + δ.toReal) +
          (μ.map a) D.haar.continuous.population.rootsᶜ ∧
        ∀ i c,
          let Qc := Q i (reference i c)
          let R := populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a
          let P₀ := D.originalWindowReferenceWeights γ gap I i (reference i c) Qc η
          let m := (κ (D.haar.continuous.coefficient i).seedIndex).restrict (R '' cell i c)
          ∃ classify : ℝ → Fin Qc.count, Measurable classify ∧
            (∀ j x, x ∈ Qc.cell j → classify x = j) ∧
            (((χ.map (Prod.map b₀ b₀)).map Prod.fst).restrict (a ⁻¹' cell i c)).map
              (fun x ↦ (R (a x), classify (u x))) = m.prod ((clockClassPairMeasure P₀).map Prod.fst) ∧
            (((χ.map (Prod.map b₀ b₀)).map Prod.snd).restrict (a ⁻¹' cell i c)).map
              (fun x ↦ (R (a x), classify (u x))) = m.prod ((clockClassPairMeasure P₀).map Prod.snd) := by
  classical
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨N, reference, cell, Pf, Qf, hcell, hsub, hmP, hmQ, hflows, hweights, hform, hglobal⟩ :=
    exists_original_clockClass_weight_sampling_population_with_inverse γ gap I D hcomplete
      hA ha hu hclockOrder hμA hνA hb₀ hμinv hνinv π hπ hlabel hforward
      hI hgap Q V hVopen hVself hδ hδ1 η ε hη hη1 hε
  refine ⟨N, reference, cell, Pf, Qf, hcell, hsub, hmP, hmQ, hflows, hweights, hform, ?_⟩
  dsimp only at hglobal ⊢
  obtain ⟨hdisj, hunion, Qglobal, hQglobal, hwhole, ξ, hπnew, hcal, hξ, hbound⟩ := hglobal
  let _instGlobal : IsSFiniteKernel Qglobal := hQglobal
  refine ⟨hdisj, hunion, Qglobal, hQglobal, hwhole, ξ, hπnew, hcal, hξ, hbound, ?_⟩
  obtain ⟨_, _, hbalance, _, _, _⟩ := exists_original_clockPair_kernel μ ν π hπ a u ha hu
    hlabel 0 (hforward.mono fun p hp ↦ sub_nonneg.mpr hp)
  intro i c
  let Qc := Q i (reference i c)
  let R := populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a
  let P₀ := D.originalWindowReferenceWeights γ gap I i (reference i c) Qc η
  obtain ⟨classify, hm, hclass, _, _, hrawS, hrawT⟩ :=
    D.exists_actual_retained_haar_class_observation hF hcomplete huLip ha hinj i (hcell i c)
      (fun z hz ↦ (hsub i c hz).1) Qc (fun _ ↦ 0) (fun _ ↦ 0) P₀
      (hweights i c).1 (hweights i c).2.2.2 (Pf i c) (Qf i c) (hmP i c) (hform i c)
      ((ae_restrict_mem (hcell i c)).mono fun z hz ↦ (hflows i c z hz).2.1)
      ((ae_restrict_mem (hcell i c)).mono fun z hz ↦ (hflows i c z hz).2.2.1)
      ((ae_restrict_mem (hcell i c)).mono fun z hz ↦ (hflows i c z hz).2.2.2.1)
  refine ⟨classify, hm, hclass, ?_, ?_⟩
  · have h := original_global_retained_cell_observation μ ν (μ.map a) a u ha hu
      b₀ hb₀ hμinv hνinv rfl hbalance.symm
      (fun c : Sigma (fun i ↦ Fin (N i)) ↦ cell c.1 c.2) (fun c ↦ hcell c.1 c.2) hdisj
      (fun c ↦ finiteClassPopulationKernel (Pf c.1 c.2)
        (fun j ↦ normalizedActualBinKernel (condDistrib u a μ)
          ((Q c.1 (reference c.1 c.2)).cell j) ((Q c.1 (reference c.1 c.2)).measurable_cell j) 0)
        (fun k ↦ normalizedActualBinKernel (condDistrib u a ν)
          ((Q c.1 (reference c.1 c.2)).cell k) ((Q c.1 (reference c.1 c.2)).measurable_cell k) 0))
      Qglobal hwhole R (measurable_populationSeedRootLabelValue _ hF hcomplete huLip ha hinj)
      classify hm ⟨i, c⟩ false
    exact h.trans hrawS
  · have h := original_global_retained_cell_observation μ ν (μ.map a) a u ha hu
      b₀ hb₀ hμinv hνinv rfl hbalance.symm
      (fun c : Sigma (fun i ↦ Fin (N i)) ↦ cell c.1 c.2) (fun c ↦ hcell c.1 c.2) hdisj
      (fun c ↦ finiteClassPopulationKernel (Pf c.1 c.2)
        (fun j ↦ normalizedActualBinKernel (condDistrib u a μ)
          ((Q c.1 (reference c.1 c.2)).cell j) ((Q c.1 (reference c.1 c.2)).measurable_cell j) 0)
        (fun k ↦ normalizedActualBinKernel (condDistrib u a ν)
          ((Q c.1 (reference c.1 c.2)).cell k) ((Q c.1 (reference c.1 c.2)).measurable_cell k) 0))
      Qglobal hwhole R (measurable_populationSeedRootLabelValue _ hF hcomplete huLip ha hinj)
      classify hm ⟨i, c⟩ true
    exact h.trans hrawT

end OTSelector.Reconstruction

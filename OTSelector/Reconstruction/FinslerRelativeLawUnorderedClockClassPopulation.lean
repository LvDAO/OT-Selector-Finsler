import OTSelector.Reconstruction.FinslerRelativeLawWindowSamplingClassPopulation
import OTSelector.Finite.OrderedBinGraph
import OTSelector.Reconstruction.FiniteScalarBins
import OTSelector.Transport.Coupling.ClassFlowReindex

/-!
Actual full clock-bin population splitting preserves the original bin
enumeration. The finite proof sorts threshold graphs and then returns the
original class matrices and raw-clock kernels, with no ordered-enumeration or
finite Hall premise.
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
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b₀ : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- The original full clock bins need no prescribed enumeration order. Sorting
only proves the legal residual flow; all returned matrices, normalized raw-clock
kernels, physical marginals and small residual use the unchanged original bins. -/
theorem exists_original_unordered_clockClass_sampling_population_with_inverse
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ) (I : Set ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b₀
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
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
    (hδ : δ ≠ ⊤)
    (η ε : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε) :
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
      (∀ i c z, z ∈ cell i c → ∀ j k, Pf i c z j k = maskedClockFlow
        (fun j k ↦ (((Q i (reference i c)).cell j ×ˢ (Q i (reference i c)).cell k) ∩
          (D.haar.continuous.coefficient i).window.region).Nonempty)
        (fun j k ↦ (1 - η) * (D.rootIntensity i (reference i c).val *
          actualClockClassFlow (γ (reference i c).val) (Q i (reference i c)).cell (Q i (reference i c)).cell j k) /
            D.rootIntensity i z) j k) ∧
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
          (μ.map a) D.haar.continuous.population.rootsᶜ := by
  classical
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  have hsort (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots) :=
    exists_ordered_legal_clockBin_graph (Q i ref).cell (Q i ref).cell
      (fun j ↦ hI.bddAbove.mono ((Q i ref).subset j))
      (fun k ↦ hI.bddBelow.mono ((Q i ref).subset k)) gap hgap
      (Q i ref).diameter (Q i ref).diameter
  choose e f horder hbins hlegal using hsort
  let S := fun i ref j ↦ (Q i ref).cell (e i ref j)
  let T := fun i ref k ↦ (Q i ref).cell (f i ref k)
  let allowed := fun i ref j k ↦ sSup ((Q i ref).cell (e i ref j)) + gap / 2 ≤
    sInf ((Q i ref).cell (f i ref k))
  have hdisjS : ∀ i ref, Pairwise (Disjoint on S i ref) := by
    intro i ref j k hjk
    exact (Q i ref).disjoint (fun heq ↦ hjk ((e i ref).injective heq))
  have hdisjT : ∀ i ref, Pairwise (Disjoint on T i ref) := by
    intro i ref j k hjk
    exact (Q i ref).disjoint (fun heq ↦ hjk ((f i ref).injective heq))
  have hcoverS : ∀ i ref, I ⊆ ⋃ j, S i ref j := by
    intro i ref s hs
    obtain ⟨j, hj⟩ := mem_iUnion.mp ((Q i ref).union_eq.symm ▸ hs)
    exact mem_iUnion.mpr ⟨(e i ref).symm j, by simpa only [S, Equiv.apply_symm_apply] using hj⟩
  have hcoverT : ∀ i ref, I ⊆ ⋃ k, T i ref k := by
    intro i ref s hs
    obtain ⟨k, hk⟩ := mem_iUnion.mp ((Q i ref).union_eq.symm ▸ hs)
    exact mem_iUnion.mpr ⟨(f i ref).symm k, by simpa only [T, Equiv.apply_symm_apply] using hk⟩
  obtain ⟨N, reference, cell, Pg, Qg, hcell, hsub, hmP, hmQ, hflows, hform, hglobal⟩ :=
    exists_original_window_reference_sampling_class_population_with_inverse γ gap I D hcomplete
      hA ha hu hclockOrder hμA hνA hb₀ hμinv hνinv π hπ hlabel hforward
      (fun i ref ↦ (Q i ref).count) (fun i ref ↦ (Q i ref).count) S T
      (fun i ref j ↦ (Q i ref).measurable_cell _) (fun i ref k ↦ (Q i ref).measurable_cell _)
      allowed horder V hVopen hVself hdisjS hdisjT hcoverS hcoverT hbins hlegal hgap.le hδ
      η ε hη hη1 hε
  let Pf := fun i c z j k ↦ Pg i c z ((e i (reference i c)).symm j) ((f i (reference i c)).symm k)
  let Qf := fun i c z j k ↦ Qg i c z ((e i (reference i c)).symm j) ((f i (reference i c)).symm k)
  refine ⟨N, reference, cell, Pf, Qf, hcell, hsub, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i c j k ↦ hmP i c _ _
  · exact fun i c j k ↦ hmQ i c _ _
  · intro i c z hz
    obtain ⟨hp, hq, hr, hc, hzero, hm⟩ := hflows i c z hz
    have hrc := originalClassFlow_unsort_rows_cols (e i (reference i c)) (f i (reference i c))
      (Pg i c z) (Qg i c z)
      (fun j ↦ (condDistrib u a μ z).real ((Q i (reference i c)).cell j))
      (fun k ↦ (condDistrib u a ν z).real ((Q i (reference i c)).cell k)) hr hc
    refine ⟨fun j k ↦ hp _ _, fun j k ↦ hq _ _, hrc.1, hrc.2, ?_, ?_⟩
    · intro j k hjk
      exact hzero _ _ (by simpa only [allowed, Equiv.apply_symm_apply] using hjk)
    · dsimp only [Qf]
      simp_rw [(f i (reference i c)).symm.sum_comp]
      rw [(e i (reference i c)).symm.sum_comp (fun j ↦ ∑ k, Qg i c z j k)]
      exact hm
  · intro i c z hz j k
    have h := hform i c z hz ((e i (reference i c)).symm j) ((f i (reference i c)).symm k)
    simpa only [Pf, S, T, maskedClockFlow, actualClockClassFlow, Equiv.apply_symm_apply] using h
  · dsimp only at hglobal ⊢
    have hKP (c : Sigma (fun i ↦ Fin (N i))) :
        finiteClassPopulationKernel (Pf c.1 c.2)
          (fun j ↦ normalizedActualBinKernel (condDistrib u a μ)
            ((Q c.1 (reference c.1 c.2)).cell j) ((Q c.1 (reference c.1 c.2)).measurable_cell j) 0)
          (fun k ↦ normalizedActualBinKernel (condDistrib u a ν)
            ((Q c.1 (reference c.1 c.2)).cell k) ((Q c.1 (reference c.1 c.2)).measurable_cell k) 0) =
        finiteClassPopulationKernel (Pg c.1 c.2)
          (fun j ↦ normalizedActualBinKernel (condDistrib u a μ) (S c.1 (reference c.1 c.2) j)
            ((Q c.1 (reference c.1 c.2)).measurable_cell _) 0)
          (fun k ↦ normalizedActualBinKernel (condDistrib u a ν) (T c.1 (reference c.1 c.2) k)
            ((Q c.1 (reference c.1 c.2)).measurable_cell _) 0) := by
      have h := finiteClassPopulationKernel_reindex
        (e c.1 (reference c.1 c.2)).symm (f c.1 (reference c.1 c.2)).symm (Pg c.1 c.2)
        (fun j ↦ normalizedActualBinKernel (condDistrib u a μ) (S c.1 (reference c.1 c.2) j)
          ((Q c.1 (reference c.1 c.2)).measurable_cell _) 0)
        (fun k ↦ normalizedActualBinKernel (condDistrib u a ν) (T c.1 (reference c.1 c.2) k)
          ((Q c.1 (reference c.1 c.2)).measurable_cell _) 0)
      simpa only [Pf, S, T, Equiv.apply_symm_apply] using h
    have hK := funext hKP
    simpa only [hK] using hglobal

end OTSelector.Reconstruction

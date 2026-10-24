import OTSelector.Reconstruction.FinslerRelativeLawActualWindowReferenceSplit
import OTSelector.Reconstruction.FinslerRelativeLawCellFamilyPartition

/-!
Full original clock-bin reference populations are assembled across all actual
coefficient cores. Paired-window losses enter the deterministic residual once;
the whole rebuilt physical population has the unchanged original marginals and
calibration, with an explicit uniform residual mass bound.
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

/-- Actual full-clock reference splitting and original paired-window loss
produce a rebuilt calibrated physical coupling of the unchanged original
populations. Its deterministic residual has mass at most η+ε+δ.toReal plus
the original discarded label mass, uniformly over all reference cells. -/
theorem exists_original_window_reference_population
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ) (I : Set ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b₀
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {A : Set M} (hA : MeasurableSet A) (ha : Measurable a) (hu : Measurable u)
    (hinj : Injective (fun x : A ↦ (a x.val, u x.val)))
    (hclockOrder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ A, (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνA : ∀ᵐ y ∂ν, y ∈ A)
    (π : Measure (M × M)) (hπ : Vlasov.IsCoupling π μ ν)
    (hlabel : ∀ᵐ p ∂π, a p.1 = a p.2) (hforward : ∀ᵐ p ∂π, u p.1 ≤ u p.2)
    (m n : ∀ i : Fin D.haar.continuous.count, (D.haar.continuous.coefficient i).roots → ℕ)
    (S : ∀ i ref, Fin (m i ref) → Set ℝ) (T : ∀ i ref, Fin (n i ref) → Set ℝ)
    (hS : ∀ i ref j, MeasurableSet (S i ref j)) (hT : ∀ i ref k, MeasurableSet (T i ref k))
    (allowed : ∀ i ref, Fin (m i ref) → Fin (n i ref) → Prop)
    (horder : ∀ i ref j j' k k', j ≤ j' → k' ≤ k → allowed i ref j' k' → allowed i ref j k)
    (V : ∀ i : Fin D.haar.continuous.count, (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (hVopen : ∀ i ref, IsOpen (V i ref)) (hVself : ∀ i ref, ref.val ∈ V i ref)
    (hdS : ∀ i ref, Pairwise (Disjoint on S i ref))
    (hdT : ∀ i ref, Pairwise (Disjoint on T i ref))
    (hcoverS : ∀ i ref, I ⊆ ⋃ j, S i ref j) (hcoverT : ∀ i ref, I ⊆ ⋃ k, T i ref k)
    (hbins : ∀ i ref j k, ∀ s ∈ S i ref j, ∀ t ∈ T i ref k,
      gap ≤ t - s → allowed i ref j k)
    (hbinLegal : ∀ i ref j k, allowed i ref j k → ∀ s ∈ S i ref j, ∀ t ∈ T i ref k, s ≤ t)
    (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤)
    (η ε : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε) :
    ∃ (N : Fin D.haar.continuous.count → ℕ)
      (reference : ∀ i, Fin (N i) → (D.haar.continuous.coefficient i).roots)
      (cell : ∀ i, Fin (N i) → Set (ℚ → M))
      (Pf : ∀ i c, (ℚ → M) → Fin (m i (reference i c)) → Fin (n i (reference i c)) → ℝ)
      (hcell : ∀ i c, MeasurableSet (cell i c)),
      (∀ i c, cell i c ⊆ (D.haar.continuous.coefficient i).roots ∩ V i (reference i c)) ∧
      (∀ i c j k, Measurable (fun z ↦ Pf i c z j k)) ∧
      (∀ i c z, z ∈ cell i c → ∀ j k, Pf i c z j k = maskedClockFlow
        (fun j k ↦ ((S i (reference i c) j ×ˢ T i (reference i c) k) ∩
          (D.haar.continuous.coefficient i).window.region).Nonempty)
        (fun j k ↦ (1 - η) * (D.rootIntensity i (reference i c).val *
          actualClockClassFlow (γ (reference i c).val) (S i (reference i c)) (T i (reference i c)) j k) /
            D.rootIntensity i z) j k) ∧
      let C := Sigma (fun i ↦ Fin (N i))
      let cells := fun c : C ↦ cell c.1 c.2
      let hcells := fun c : C ↦ hcell c.1 c.2
      let α := fun (c : C) j ↦ normalizedActualBinKernel (condDistrib u a μ)
        (S c.1 (reference c.1 c.2) j) (hS c.1 (reference c.1 c.2) j) 0
      let β := fun (c : C) k ↦ normalizedActualBinKernel (condDistrib u a ν)
        (T c.1 (reference c.1 c.2) k) (hT c.1 (reference c.1 c.2) k) 0
      let KP := fun c : C ↦ finiteClassPopulationKernel (Pf c.1 c.2) (α c) (β c)
      let χ := ((μ.map a) ⊗ₘ finiteCellPairKernel cells hcells KP).map sameLabelPopulationPair
      let _inst : MetricSpace M := F.metricSpace
      ∃ (b : (ℚ → M) × ℝ → M) (ξ : Measure (M × M)), Measurable b ∧
        Vlasov.IsCoupling (χ.map (Prod.map b b) + ξ) μ ν ∧
        (∀ᵐ p ∂χ.map (Prod.map b b) + ξ, u p.2 - u p.1 = dist p.1 p.2) ∧
        ξ ≤ χ.map (Prod.map b b) + ξ ∧
        ξ univ ≤ ENNReal.ofReal (η + ε + δ.toReal) +
          (μ.map a) D.haar.continuous.population.rootsᶜ := by
  classical
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  have hlocal (i : Fin D.haar.continuous.count) :=
    D.exists_measurable_actual_window_classSplit_cells γ gap I hcomplete i (m i) (n i)
      (S i) (T i) (hS i) (hT i) (allowed i) (horder i) (V i) (hVopen i) (hVself i)
      (hdS i) (hdT i) (hcoverS i) (hcoverT i) (hbins i) hgap hδ η ε hη hη1 hε
  choose N reference cell Pf Qf hcell hdisj hunion hsub hmP hmQ hsplit using hlocal
  have hpart := sigma_cell_partition (fun i ↦ (D.haar.continuous.coefficient i).roots)
    D.haar.continuous.disjoint N cell hdisj hunion
  have hunionAll : (⋃ c : Sigma (fun i ↦ Fin (N i)), cell c.1 c.2) =
      D.haar.continuous.population.roots := hpart.2.trans D.haar.continuous.union_eq
  refine ⟨N, reference, cell, Pf, hcell, hsub, hmP, ?_, ?_⟩
  · intro i c z hz j k
    exact (hsplit i c z hz).2.2.2.2.2.2 j k
  · dsimp only
    have hcoverμ : ∀ᵐ z ∂μ.map a, ∀ c : Sigma (fun i ↦ Fin (N i)), z ∈ cell c.1 c.2 →
        ∀ᵐ s ∂condDistrib u a μ z, s ∈ ⋃ j, S c.1 (reference c.1 c.2) j := by
      exact Filter.Eventually.of_forall fun z c hz ↦
        (((D.haar.continuous.population.good z
          (hunionAll ▸ mem_iUnion.mpr ⟨c, hz⟩)).1).2.2.1).mono
            (fun s hs ↦ hcoverS c.1 (reference c.1 c.2) hs)
    have hcoverν : ∀ᵐ z ∂μ.map a, ∀ c : Sigma (fun i ↦ Fin (N i)), z ∈ cell c.1 c.2 →
        ∀ᵐ t ∂condDistrib u a ν z, t ∈ ⋃ k, T c.1 (reference c.1 c.2) k := by
      exact Filter.Eventually.of_forall fun z c hz ↦
        (((D.haar.continuous.population.good z
          (hunionAll ▸ mem_iUnion.mpr ⟨c, hz⟩)).1).2.2.2).mono
            (fun t ht ↦ hcoverT c.1 (reference c.1 c.2) ht)
    have hflows : ∀ᵐ z ∂μ.map a, ∀ c : Sigma (fun i ↦ Fin (N i)), z ∈ cell c.1 c.2 →
        (∀ j k, 0 ≤ Pf c.1 c.2 z j k) ∧ (∀ j k, 0 ≤ Qf c.1 c.2 z j k) ∧
        (∀ j, ∑ k, (Pf c.1 c.2 z j k + Qf c.1 c.2 z j k) =
          (condDistrib u a μ z).real (S c.1 (reference c.1 c.2) j)) ∧
        (∀ k, ∑ j, (Pf c.1 c.2 z j k + Qf c.1 c.2 z j k) =
          (condDistrib u a ν z).real (T c.1 (reference c.1 c.2) k)) ∧
        (∀ j k, ¬ allowed c.1 (reference c.1 c.2) j k →
          Pf c.1 c.2 z j k = 0 ∧ Qf c.1 c.2 z j k = 0) ∧
        (∑ j, ∑ k, Qf c.1 c.2 z j k) ≤ η + ε + δ.toReal := by
      exact Filter.Eventually.of_forall fun z c hz ↦
        let h := hsplit c.1 c.2 z hz
        ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
    have h := exists_original_cellwise_bin_residual_population hA ha hu hinj hclockOrder
      μ ν hμA hνA π hπ hlabel hforward
      (fun c : Sigma (fun i ↦ Fin (N i)) ↦ cell c.1 c.2)
      (fun c ↦ hcell c.1 c.2) hpart.1
      (fun c ↦ Fin (m c.1 (reference c.1 c.2))) (fun c ↦ Fin (n c.1 (reference c.1 c.2)))
      (fun c ↦ S c.1 (reference c.1 c.2)) (fun c ↦ T c.1 (reference c.1 c.2))
      (fun c ↦ hS c.1 (reference c.1 c.2)) (fun c ↦ hT c.1 (reference c.1 c.2))
      (fun c ↦ hdS c.1 (reference c.1 c.2)) (fun c ↦ hdT c.1 (reference c.1 c.2))
      hcoverμ hcoverν (fun _ _ ↦ 0) (fun _ _ ↦ 0)
      (fun c ↦ allowed c.1 (reference c.1 c.2))
      (fun c ↦ hbinLegal c.1 (reference c.1 c.2))
      (fun c ↦ Pf c.1 c.2) (fun c ↦ Qf c.1 c.2)
      (fun c ↦ hmP c.1 c.2) (fun c ↦ hmQ c.1 c.2)
      (η + ε + δ.toReal) hflows
    simpa only [hunionAll] using h

end OTSelector.Reconstruction

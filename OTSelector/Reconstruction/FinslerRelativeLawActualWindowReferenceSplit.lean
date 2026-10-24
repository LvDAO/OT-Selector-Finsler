import OTSelector.Reconstruction.FinslerRelativeLawActualDependentReferenceSplit
import OTSelector.Transport.Coupling.MeasurableWindowTransfer

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

/-- Original scalar-window pair loss is moved into the measurable deterministic
residual, after full original-clock finite-bin splitting. Exact conditional
marginals persist and the uniform residual mass is η+ε+δ.toReal. -/
theorem PopulationLocalPressureCore.exists_measurable_actual_window_classSplit_cells
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
    (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤)
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
        (∑ j, ∑ k, Qf c z j k) ≤ η + ε + δ.toReal ∧
        ∀ j k, Pf c z j k = maskedClockFlow
          (fun j k ↦ ((S (reference c) j ×ˢ T (reference c) k) ∩
            (D.haar.continuous.coefficient i).window.region).Nonempty)
          (fun j k ↦ (1 - η) * (D.rootIntensity i (reference c).val *
            actualClockClassFlow (γ (reference c).val) (S (reference c)) (T (reference c)) j k) /
              D.rootIntensity i z) j k := by
  classical
  let K := (D.haar.continuous.coefficient i).roots
  have hgood (z) (hz : z ∈ K) : originalClockPairGood γ
      (condDistrib u a η₀) (condDistrib u a η₁) gap I z := by
    apply (D.haar.continuous.population.good z _).1
    exact D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i, hz⟩
  have hfeasible (ref : K) (z) (hz : z ∈ K) :=
    actualClockClassFlow_original_feasible_at (γ z)
      (condDistrib u a η₀ z) (condDistrib u a η₁ z) (hgood z hz).1
      (S ref) (T ref) (hS ref) (hT ref) (hdS ref) (hdT ref)
      ((hgood z hz).2.2.1.mono (fun s hs ↦ hcoverS ref hs))
      ((hgood z hz).2.2.2.mono (fun t ht ↦ hcoverT ref ht))
      (allowed ref) (fun p ↦ gap ≤ p.2 - p.1) (hgood z hz).2.1 (hbins ref)
  obtain ⟨N, reference, cell, Pold, Qold, hcell, hdisj, hunion, hsub, hmP, hmQ, hsplit⟩ :=
    D.exists_measurable_actual_reference_classSplit_cells γ gap I hcomplete i m n S T hS hT
      allowed horder V hVopen hVself hdS hdT hcoverS hcoverT hbins η ε hη hη1 hε
  have htransfer (c : Fin N) : ∃ Pg Qg : (ℚ → M) → Fin (m (reference c)) → Fin (n (reference c)) → ℝ,
      (∀ j k, Measurable (fun z ↦ Pg z j k)) ∧
      (∀ j k, Measurable (fun z ↦ Qg z j k)) ∧
      ∀ z ∈ cell c,
        (∀ j k, 0 ≤ Pg z j k) ∧ (∀ j k, 0 ≤ Qg z j k) ∧
        (∀ j, ∑ k, (Pg z j k + Qg z j k) =
          (populationTwoColorClockKernel u a η₀ η₁ 0 z).real (S (reference c) j)) ∧
        (∀ k, ∑ j, (Pg z j k + Qg z j k) =
          (populationTwoColorClockKernel u a η₀ η₁ 1 z).real (T (reference c) k)) ∧
        (∀ j k, ¬ allowed (reference c) j k → Pg z j k = 0 ∧ Qg z j k = 0) ∧
        (∑ j, ∑ k, Qg z j k) ≤ η + ε + δ.toReal ∧
        ∀ j k, Pg z j k = maskedClockFlow
          (fun j k ↦ ((S (reference c) j ×ˢ T (reference c) k) ∩
            (D.haar.continuous.coefficient i).window.region).Nonempty) (Pold c z) j k := by
    let ref := reference c
    apply exists_measurable_actualReferenceWindow_split
      (γ ref.val) (S ref) (T ref) (hS ref) (hT ref) (hdS ref) (hdT ref)
      (D.haar.continuous.coefficient i).window.region (allowed ref)
      (Pold c) (Qold c) (hmP c) (hmQ c)
      (fun z j ↦ (populationTwoColorClockKernel u a η₀ η₁ 0 z).real (S ref j))
      (fun z k ↦ (populationTwoColorClockKernel u a η₀ η₁ 1 z).real (T ref k))
      (cell c) (η + ε) δ.toReal (hfeasible ref ref.val ref.property).2.2.2.2
    · have hl := (D.haar.continuous.coefficient i).coupling_loss ref.val ref.property
        (γ ref.val) (hgood ref.val ref.property).1
        ((hgood ref.val ref.property).2.1.mono (fun p hp ↦ by linarith))
      exact ENNReal.toReal_mono hδ hl.le
    · intro z hz
      obtain ⟨hp, hq, hr, hc, hzero, hm, hform⟩ := hsplit c z hz
      have hzK : z ∈ K := (hsub c hz).1
      have ha := hfeasible ref z hzK
      have hatotal : ∑ j, (populationTwoColorClockKernel u a η₀ η₁ 0 z).real (S ref j) = 1 := by
        change (∑ j, (condDistrib u a η₀ z).real (S ref j)) = 1
        simp_rw [← ha.2.1]
        exact ha.2.2.2.2
      refine ⟨hp, hq, hr, hc, ?_, hm, hatotal, ?_⟩
      · intro j k hn
        exact ⟨(hfeasible ref ref.val ref.property).2.2.2.1 j k hn, (hzero j k hn).2⟩
      · refine ⟨(1 - η) * D.rootIntensity i ref.val / D.rootIntensity i z, ?_⟩
        intro j k
        rw [hform]
        ring
  choose Pg Qg hmPg hmQg hnew using htransfer
  refine ⟨N, reference, cell, Pg, Qg, hcell, hdisj, hunion, hsub, hmPg, hmQg, ?_⟩
  intro c z hz
  obtain ⟨hp, hq, hr, hc, hzero, hm, hform⟩ := hnew c z hz
  refine ⟨hp, hq, hr, hc, hzero, hm, ?_⟩
  intro j k
  rw [hform]
  have he : Pold c z = fun j k ↦ (1 - η) * (D.rootIntensity i (reference c).val *
      actualClockClassFlow (γ (reference c).val) (S (reference c)) (T (reference c)) j k) /
        D.rootIntensity i z := by
    funext j k
    exact (hsplit c z hz).2.2.2.2.2.2 j k
  rw [he]

end OTSelector.Reconstruction

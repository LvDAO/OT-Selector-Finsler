import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedFullTail
import OTSelector.Reconstruction.FinslerPhysicalSceneClockScreenOriginal

/-!
# Actual tail tightness in the same original fixed seed scene

The original optimal face supplies an auxiliary accuracy core.  Its finite near
coefficient determines a fixed large threshold; the original increasing spatial
scale then removes the remaining energy term.  Neither the physical scene nor
the two-index allocations change with this accuracy choice.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Auxiliary accuracy, a fixed large threshold, and only afterward the
original scale control all indexed readouts uniformly. -/
theorem eventually_uniform_tail_small_of_auxiliary_energy_bounds
    {I : Type*} (mass : I → ℕ → ℝ≥0∞ → ℝ≥0∞)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (V C : ℝ≥0∞) (hV : V ≠ ⊤) (hC : C ≠ ⊤)
    (hbound : ∀ δ : ℝ≥0, 0 < δ → ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∃ c > 0,
      ∀ i n threshold, threshold ≠ 0 → threshold ≠ ⊤ →
        mass i n threshold ≤ K / threshold +
          V * ((δ : ℝ≥0∞) + C / ENNReal.ofReal (scale n * c))) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ threshold : ℝ≥0∞,
      0 < threshold ∧ threshold ≠ ⊤ ∧
        ∀ᶠ n in atTop, ∀ i, mass i n threshold ≤ ε := by
  intro ε hε
  have hthird : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨δ, hδ, hδV⟩ := ENNReal.exists_nnreal_pos_mul_lt hV hthird.ne'
  obtain ⟨K, hK, c, hc, hb⟩ := hbound δ hδ
  have hnear : Tendsto (fun m : ℕ ↦ K / (m : ℝ≥0∞)) atTop (𝓝 0) := by
    simpa only [ENNReal.div_top] using
      (ENNReal.Tendsto.div tendsto_const_nhds (Or.inr (by simp))
        ENNReal.tendsto_nat_nhds_top (Or.inr hK))
  obtain ⟨m, hm1, hmε⟩ := ((eventually_ge_atTop 1).and
    ((ENNReal.tendsto_nhds_zero.mp hnear) (ε / 3) hthird)).exists
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm1
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hmt : (m : ℝ≥0∞) ≠ ⊤ := by simp
  refine ⟨(m : ℝ≥0∞), by exact_mod_cast hmpos, hmt, ?_⟩
  have hden : Tendsto (fun n ↦ ENNReal.ofReal (scale n * c)) atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_nhds_top.mpr (hscale.atTop_mul_const hc)
  have hdiv : Tendsto (fun n ↦ C / ENNReal.ofReal (scale n * c)) atTop (𝓝 0) := by
    simpa only [ENNReal.div_top] using
      (ENNReal.Tendsto.div tendsto_const_nhds (Or.inr (by simp)) hden (Or.inr hC))
  have hterm : Tendsto (fun n ↦ V * (C / ENNReal.ofReal (scale n * c))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (ENNReal.continuousAt_const_mul (Or.inl hV)).tendsto.comp hdiv
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hterm) (ε / 3) hthird] with n hn i
  calc
    mass i n m ≤ K / m + V * ((δ : ℝ≥0∞) + C / ENNReal.ofReal (scale n * c)) := hb i n m hm0 hmt
    _ = (K / m + V * (δ : ℝ≥0∞)) + V * (C / ENNReal.ofReal (scale n * c)) := by rw [mul_add, add_assoc]
    _ ≤ (ε / 3 + ε / 3) + ε / 3 :=
      add_le_add (add_le_add hmε (by simpa only [mul_comm] using hδV.le)) hn
    _ = ε := by
      calc
        _ = 3 * (ε / 3) := by ring
        _ = _ := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}

/-- Original physical data produce actual tail tightness for both original
allocations, in both rooted windows, uniformly in the tilt index.  The auxiliary
core is chosen before the threshold, and the threshold before the sample size. -/
theorem exists_original_fixed_seed_uniform_both_tail_tightness
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
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
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (j : ℕ)
    (aplus aminus : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hplus : ∀ ℓ n k, Measurable (fun z : (((Fin (n + 1) → M) ×
      (Fin (n + 1) → ℝ)) × M) ↦ aplus ℓ n z.1 z.2 k))
    (hminus : ∀ ℓ n k, Measurable (fun z : (((Fin (n + 1) → M) ×
      (Fin (n + 1) → ℝ)) × M) ↦ aminus ℓ n z.1 z.2 k))
    (hfp : ∀ ℓ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (aplus ℓ n z))
    (hfm : ∀ ℓ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (aminus ℓ n z))
    (spatialScale : ℕ → ℝ) (hsp : ∀ n, 0 < spatialScale n)
    (hscale : Tendsto (fun n ↦ spatialScale n ^ 2) atTop atTop)
    (rootMass : ℕ → ℝ) (hN : ∀ n, 0 < rootMass n)
    (rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hRoot : ∀ n, volume (rootDomain n) = ENNReal.ofReal (rootMass n))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hEp : ∀ ℓ n, (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
      ∂physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (fun z ↦ z.1) w
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C)
    (hEm : ∀ ℓ n, (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
      ∂physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (fun z ↦ z.1) w
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C)
    (U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hU : MeasurableSet U) (hUf : volume U ≠ ⊤) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
    let sourceTail := fun (n : ℕ)
      (allocation : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
      (threshold : ℝ≥0∞) ↦
      ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ allocation (fun z ↦ z.1) w).restrict (H ×ˢ univ))
        (coord n) u (rootMass n) z (physicalSceneLongEdgeWindow U threshold)
        ∂cavityRootMeasure volume (rootDomain n) (rootMass n)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
    let targetTail := fun (n : ℕ)
      (allocation : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
      (threshold : ℝ≥0∞) ↦
      ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ allocation (fun z ↦ z.1) w).restrict (H ×ˢ univ))
        (coord n) u (rootMass n) z (physicalSceneTargetLongEdgeWindow U threshold)
        ∂cavityRootMeasure volume (rootDomain n) (rootMass n)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ threshold : ℝ≥0∞,
      0 < threshold ∧ threshold ≠ ⊤ ∧ ∀ᶠ n in atTop, ∀ ℓ,
        (sourceTail n (aplus ℓ n) threshold ≤ ε ∧ targetTail n (aplus ℓ n) threshold ≤ ε) ∧
        (sourceTail n (aminus ℓ n) threshold ≤ ε ∧ targetTail n (aminus ℓ n) threshold ≤ ε) := by
  let _inst : MetricSpace M := F.metricSpace
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
  let sourceTail := fun (n : ℕ)
    (allocation : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (threshold : ℝ≥0∞) ↦
    ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily μ allocation (fun z ↦ z.1) w).restrict (H ×ˢ univ))
      (coord n) u (rootMass n) z (physicalSceneLongEdgeWindow U threshold)
      ∂cavityRootMeasure volume (rootDomain n) (rootMass n)
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
  let targetTail := fun (n : ℕ)
    (allocation : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (threshold : ℝ≥0∞) ↦
    ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily μ allocation (fun z ↦ z.1) w).restrict (H ×ˢ univ))
      (coord n) u (rootMass n) z (physicalSceneTargetLongEdgeWindow U threshold)
      ∂cavityRootMeasure volume (rootDomain n) (rootMass n)
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
  let mass := fun ℓ n threshold ↦
    max (max (sourceTail n (aplus ℓ n) threshold) (targetTail n (aplus ℓ n) threshold))
      (max (sourceTail n (aminus ℓ n) threshold) (targetTail n (aminus ℓ n) threshold))
  have hsmall := eventually_uniform_tail_small_of_auxiliary_energy_bounds mass
    (fun n ↦ spatialScale n ^ 2) hscale (volume U) C hUf hC (by
      intro δ hδ
      let d : ℝ≥0∞ := (δ : ℝ≥0∞) / 4
      have hd : 0 < d := ENNReal.div_pos (by exact_mod_cast hδ.ne') (by norm_num)
      obtain ⟨D, hscreen, hμtail, hνtail⟩ :=
        exists_original_small_clock_screen_population_core_of_face hcore hrecovery
          hF hcomplete hu ha hinj hκ hbalance hA hB hμ hν hreg hμreg hface
          (half_pos hgap) hd.ne' hd.ne'
      have htails : μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ ≤
          (δ : ℝ≥0∞) := by
        apply (add_le_add hμtail hνtail).trans_eq
        calc
          _ = 4 * ((δ : ℝ≥0∞) / 4) := by dsimp only [d]; ring
          _ = _ := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
      obtain ⟨q, hq, c, hc, hb⟩ := D.exists_original_fixed_seed_both_full_longTail_bounds
        hF hcomplete hu ha hinj horder hA.measurableSet hB.measurableSet hμ hν hgap hdist hscreen
      let K := (D.haar.continuous.count : ℝ≥0∞) * (volume U * (C / ENNReal.ofReal q))
      have hK : K ≠ ⊤ := ENNReal.mul_ne_top (by simp)
        (ENNReal.mul_ne_top hUf (ENNReal.div_ne_top hC (ENNReal.ofReal_ne_zero_iff.mpr hq)))
      refine ⟨K, hK, c, hc, ?_⟩
      intro ℓ n threshold ht0 htt
      have hp := hb j n (aplus ℓ n) (hplus ℓ n) (hfp ℓ n)
        (spatialScale n) (rootMass n) (hsp n) (hN n) (rootDomain n) U (hRoot n) hU hUf
        threshold ht0 htt C (hEp ℓ n)
      have hm := hb j n (aminus ℓ n) (hminus ℓ n) (hfm ℓ n)
        (spatialScale n) (rootMass n) (hsp n) (hN n) (rootDomain n) U (hRoot n) hU hUf
        threshold ht0 htt C (hEm ℓ n)
      have hnum :
          (D.haar.continuous.count : ℝ≥0∞) * ((volume U * (C / ENNReal.ofReal q)) / threshold) +
            volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
              C / ENNReal.ofReal (spatialScale n ^ 2 * c)) ≤
          K / threshold + volume U * ((δ : ℝ≥0∞) +
            C / ENNReal.ofReal (spatialScale n ^ 2 * c)) := by
        calc
          _ ≤ (D.haar.continuous.count : ℝ≥0∞) * ((volume U * (C / ENNReal.ofReal q)) / threshold) +
              volume U * ((δ : ℝ≥0∞) + C / ENNReal.ofReal (spatialScale n ^ 2 * c)) :=
            add_le_add le_rfl (mul_le_mul_right (add_le_add htails le_rfl) _)
          _ = _ := by simp only [K, div_eq_mul_inv, mul_assoc]
      exact max_le (max_le (hp.1.trans hnum) (hp.2.trans hnum))
        (max_le (hm.1.trans hnum) (hm.2.trans hnum)))
  dsimp only
  intro ε hε
  obtain ⟨threshold, htpos, htt, ht⟩ := hsmall ε hε
  refine ⟨threshold, htpos, htt, ?_⟩
  filter_upwards [ht] with n hn ℓ
  exact ⟨max_le_iff.mp (max_le_iff.mp (hn ℓ)).1, max_le_iff.mp (max_le_iff.mp (hn ℓ)).2⟩

end OTSelector.Reconstruction

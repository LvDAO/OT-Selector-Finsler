import OTSelector.Reconstruction.OriginalIIDFixedSeedFullTail
import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedTailTightness

/-!
# Actual iid partner tails in a fixed original seed

An eventual common original slack-energy budget suffices. The physical source
piece, seed frame and actual selected iid optimizers stay fixed while an
auxiliary accuracy core, then a displacement threshold, are chosen.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}

/-- The original iid plans have eventually small source- and target-window
partner tails, uniformly over the selected cost index. Only an eventual common
true slack-energy bound is needed; no finite optimizer or input law is replaced. -/
theorem exists_originalIID_fixed_seed_uniform_both_tail_tightness
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
    (j : ℕ) {I : Type*}
    (cost : I → ℕ → M → M → ℝ)
    (hcost : ∀ ℓ n, Measurable (Function.uncurry (cost ℓ n)))
    (selectionScale : I → ℕ → ℝ)
    (spatialScale : ℕ → ℝ) (hsp : ∀ n, 0 < spatialScale n)
    (hscale : Tendsto (fun n ↦ spatialScale n ^ 2) atTop atTop)
    (rootMass : ℕ → ℝ) (hN : ∀ n, 0 < rootMass n)
    (rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hRoot : ∀ n, volume (rootDomain n) = ENNReal.ofReal (rootMass n))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergy : ∀ᶠ n in atTop, ∀ ℓ : I,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n + 1) (cost ℓ n) (selectionScale ℓ n) w
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) ≤ C)
    (U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hU : MeasurableSet U) (hUf : volume U ≠ ⊤) :
    let H := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition
      (P := P) (a := a) j (spatialScale n)
    let Penv := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
    let Γ := fun ℓ n ↦ originalIIDOptimalPhysicalPlan
      (n := n + 1) (cost ℓ n) (selectionScale ℓ n)
    let sourceTail := fun ℓ n threshold ↦ ∫⁻ w, ∫⁻ z,
      physicalSceneRootedPlan ((Γ ℓ n w).restrict (H ×ˢ univ)) (coord n) u
        (rootMass n) z (physicalSceneLongEdgeWindow U threshold)
        ∂cavityRootMeasure volume (rootDomain n) (rootMass n) ∂Penv n
    let targetTail := fun ℓ n threshold ↦ ∫⁻ w, ∫⁻ z,
      physicalSceneRootedPlan ((Γ ℓ n w).restrict (H ×ˢ univ)) (coord n) u
        (rootMass n) z (physicalSceneTargetLongEdgeWindow U threshold)
        ∂cavityRootMeasure volume (rootDomain n) (rootMass n) ∂Penv n
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ threshold : ℝ≥0∞,
      0 < threshold ∧ threshold ≠ ⊤ ∧ ∀ᶠ n in atTop, ∀ ℓ : I,
        sourceTail ℓ n threshold ≤ ε ∧ targetTail ℓ n threshold ≤ ε := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp henergy
  let H := physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition
    (P := P) (a := a) j (spatialScale n)
  let Penv := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  let Γ := fun ℓ n ↦ originalIIDOptimalPhysicalPlan
    (n := n + 1) (cost ℓ n) (selectionScale ℓ n)
  let sourceTail := fun ℓ n threshold ↦ ∫⁻ w, ∫⁻ z,
    physicalSceneRootedPlan ((Γ ℓ n w).restrict (H ×ˢ univ)) (coord n) u
      (rootMass n) z (physicalSceneLongEdgeWindow U threshold)
      ∂cavityRootMeasure volume (rootDomain n) (rootMass n) ∂Penv n
  let targetTail := fun ℓ n threshold ↦ ∫⁻ w, ∫⁻ z,
    physicalSceneRootedPlan ((Γ ℓ n w).restrict (H ×ˢ univ)) (coord n) u
      (rootMass n) z (physicalSceneTargetLongEdgeWindow U threshold)
      ∂cavityRootMeasure volume (rootDomain n) (rootMass n) ∂Penv n
  let mass := fun ℓ n threshold ↦ if N₀ ≤ n then
    max (sourceTail ℓ n threshold) (targetTail ℓ n threshold) else 0
  have hsmall := eventually_uniform_tail_small_of_auxiliary_energy_bounds mass
    (fun n ↦ spatialScale n ^ 2) hscale (volume U) C hUf hC (by
      intro δ hδ
      let d : ℝ≥0∞ := (δ : ℝ≥0∞) / 4
      have hd : 0 < d := ENNReal.div_pos (by exact_mod_cast hδ.ne') (by norm_num)
      obtain ⟨D, hscreen, hμtail, hνtail⟩ :=
        exists_original_small_clock_screen_population_core_of_face hcore hrecovery
          hF hcomplete hu ha hinj hκ hbalance hA hB hμ hν hreg hμreg hface
          (half_pos hgap) hd.ne' hd.ne'
      have htails : μ (⋃ i, D.physicalCoreDomain i)ᶜ +
          ν (⋃ i, D.physicalCoreDomain i)ᶜ ≤ (δ : ℝ≥0∞) := by
        apply (add_le_add hμtail hνtail).trans_eq
        calc
          _ = 4 * ((δ : ℝ≥0∞) / 4) := by dsimp only [d]; ring
          _ = _ := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
      obtain ⟨q, hq, c, hc, hb⟩ :=
        D.exists_originalIID_fixed_seed_both_full_longTail_bounds
          hF hcomplete hu ha hinj horder hA.measurableSet hB.measurableSet hμ hν
          hgap hdist hscreen
      let K := (D.haar.continuous.count : ℝ≥0∞) * (volume U * (C / ENNReal.ofReal q))
      have hK : K ≠ ⊤ := ENNReal.mul_ne_top (by simp)
        (ENNReal.mul_ne_top hUf (ENNReal.div_ne_top hC (ENNReal.ofReal_ne_zero_iff.mpr hq)))
      refine ⟨K, hK, c, hc, ?_⟩
      intro ℓ n threshold ht0 htt
      by_cases hn : N₀ ≤ n
      · have hp := hb j n (cost ℓ n) (hcost ℓ n) (selectionScale ℓ n)
          (spatialScale n) (rootMass n) (hsp n) (hN n) (rootDomain n) U (hRoot n)
          hU hUf threshold ht0 htt C (hN₀ n hn ℓ)
        have hnum :
            (D.haar.continuous.count : ℝ≥0∞) *
                ((volume U * (C / ENNReal.ofReal q)) / threshold) +
              volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ +
                ν (⋃ i, D.physicalCoreDomain i)ᶜ +
                C / ENNReal.ofReal (spatialScale n ^ 2 * c)) ≤
            K / threshold + volume U * ((δ : ℝ≥0∞) +
              C / ENNReal.ofReal (spatialScale n ^ 2 * c)) := by
          calc
            _ ≤ (D.haar.continuous.count : ℝ≥0∞) *
                ((volume U * (C / ENNReal.ofReal q)) / threshold) +
                volume U * ((δ : ℝ≥0∞) +
                  C / ENNReal.ofReal (spatialScale n ^ 2 * c)) :=
              add_le_add le_rfl (mul_le_mul_right (add_le_add htails le_rfl) _)
            _ = _ := by simp only [K, div_eq_mul_inv, mul_assoc]
        simpa only [mass, ite_eq_left hn] using max_le (hp.1.trans hnum) (hp.2.trans hnum)
      · simp only [mass, ite_eq_right hn]
        exact bot_le)
  dsimp only
  intro ε hε
  obtain ⟨threshold, htpos, htt, ht⟩ := hsmall ε hε
  refine ⟨threshold, htpos, htt, ?_⟩
  filter_upwards [ht, eventually_ge_atTop N₀] with n hn hlarge ℓ
  have hm : max (sourceTail ℓ n threshold) (targetTail ℓ n threshold) ≤ ε := by
    simpa only [mass, ite_eq_left hlarge] using hn ℓ
  exact max_le_iff.mp hm

end OTSelector.Reconstruction

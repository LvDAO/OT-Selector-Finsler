import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedProbeGapRefinement
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationProbeLaw
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalIteratedProbeAgreement
import OTSelector.Probability.ProbabilityMeasureWeakSecondCountable

/-!
# Actual original allocation limits agree on the same original weak law

Each original seed uses its own refined scene extraction. The original law
limits are preserved, and exact raw-plan probe identities discharge every
readout witness in the same-law agreement theorem.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}


/-- Actual original global allocations and their same original weak stages give
full limiting agreement. No scene-law, probe-gap or source-marginal oracle is supplied. -/
theorem ae_originalAllocationPlanPairLaw_eq_of_iterated_limits_of_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hdim : 2 ≤ Module.finrank ℝ E) (m : Measure E) [m.IsAddHaarMeasure]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M}
    (nearRadius : ℝ)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n) (hscale : Tendsto scale atTop atTop)
    (hnormalization : ∀ n, scale n ^ (finrank ℝ E - 1) = (n : ℝ) + 1)
    (probe : M → M → ℝ) (hprobe : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hprobeBound : ∀ x y, |probe x y| ≤ G)
    (t : ℕ → ℝ) (ht0 : ∀ ℓ, 0 ≤ t ℓ) (ht0lim : Tendsto t atTop (𝓝 0))
    (ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 j))
    (hmm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 j))
    (hp : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
            t ℓ * probe x (w.1 j)) (ap ℓ n w))
    (hm : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
            (-t ℓ) * probe x (w.1 j)) (am ℓ n w))
    (hμlaw : PopulationConditionalWindowLaw P a κ (μ.map a) μ ρ₀ v)
    (hνlaw : PopulationConditionalWindowLaw P a κ (μ.map a) ν ρ₁ v)
    (hAsupport : IsCompact A) (hBsupport : IsCompact B) (hAB : Disjoint A B)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) (hbalance : μ.map a = ν.map a)
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
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
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    (hnearRadius : 0 < nearRadius)
    (Energy : ℝ≥0∞) (hEnergy : Energy ≠ ⊤)
    (hEp : ∀ ℓ n,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy)
    (hEm : ∀ ℓ n,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy)
    (φ₀ : ℕ → ℕ → ℕ) (hφ₀ : ∀ ℓ, StrictMono (φ₀ ℓ))
    (ψ₀ : ℕ → ℕ) (hψ₀ : StrictMono ψ₀)
    :
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instPolish : PolishSpace M := inferInstance
    let _instPlanBorel : BorelSpace (ProbabilityMeasure (M × M)) := probabilityMeasure_weakBorelSpace
    let _instPlanSecond : SecondCountableTopology (ProbabilityMeasure (M × M)) :=
      probabilityMeasure_weakSecondCountable
    let laws := fun ℓ n ↦ physicalSceneOriginalAllocationPlanPairLaw
      ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ ν
      (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
      (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
    ∀ (Q : ℕ → ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
      (R : ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
      (_hinner : ∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ₀ ℓ n)) atTop (𝓝 (Q ℓ)))
      (_houter : Tendsto (fun ℓ ↦ Q (ψ₀ ℓ)) atTop (𝓝 R))
      (_hopt₀ : ∀ᵐ s ∂(R : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))), IsOptimalCoupling edist μ ν (s.1 : Measure (M × M)))
      (_hopt₁ : ∀ᵐ s ∂(R : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))), IsOptimalCoupling edist μ ν (s.2 : Measure (M × M))),
      ∀ᵐ s ∂(R : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))), (s.1 : Measure (M × M)) = (s.2 : Measure (M × M)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instPlanBorel : BorelSpace (ProbabilityMeasure (M × M)) := probabilityMeasure_weakBorelSpace
  let _instPlanSecond : SecondCountableTopology (ProbabilityMeasure (M × M)) :=
    probabilityMeasure_weakSecondCountable
  let S := ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)
  let Penv := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let laws := fun ℓ n ↦ physicalSceneOriginalAllocationPlanPairLaw (Penv n) μ ν
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
    (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
  dsimp only
  intro Q R hinner houter hopt₀ hopt₁
  have hfp (ℓ n : ℕ) : ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ w.2 (ap ℓ n w) :=
    (hp ℓ n).mono fun _ hw ↦ hw.1
  have hfm (ℓ n : ℕ) : ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ w.2 (am ℓ n w) :=
    (hm ℓ n).mono fun _ hw ↦ hw.1
  let C : Set S := {s | (s.1 : Measure (M × M)).fst = μ ∧ (s.2 : Measure (M × M)).fst = μ}
  have hC : MeasurableSet C :=
    ((isClosed_probability_fixed_source μ).measurableSet.preimage measurable_fst).inter
      ((isClosed_probability_fixed_source μ).measurableSet.preimage measurable_snd)
  have hsource (ℓ n : ℕ) : ∀ᵐ s ∂(laws ℓ n : Measure S), s ∈ C := by
    let pair := fun w ↦
      (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν (ap ℓ n) (fun w ↦ w.1) w,
        physicalSceneOriginalAllocationProbabilityPlanFamily μ ν (am ℓ n) (fun w ↦ w.1) w)
    have hpair : Measurable pair :=
      (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν (ap ℓ n)
        (hpm ℓ n) (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)).prodMk
      (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν (am ℓ n)
        (hmm ℓ n) (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst))
    change ∀ᵐ s ∂(Penv n).map pair, s ∈ C
    apply (ae_map_iff hpair.aemeasurable hC).mpr
    filter_upwards [ae_fst_physicalSceneOriginalAllocationProbabilityPlanFamily
      (Penv n) μ ν (ap ℓ n) (fun w ↦ w.1) (fun w ↦ w.2) (hfp ℓ n),
      ae_fst_physicalSceneOriginalAllocationProbabilityPlanFamily
        (Penv n) μ ν (am ℓ n) (fun w ↦ w.1) (fun w ↦ w.2) (hfm ℓ n)] with w hp hm
    exact ⟨hp, hm⟩
  apply ae_original_plans_eq_of_seedwise_iterated_probe_gaps_of_face
    hF hcomplete hu ha hinj hμlaw horder (fun _ ↦ inferInstance) hface R
    Prod.fst Prod.snd continuous_fst continuous_snd hopt₀ hopt₁
  intro j
  have hdimKer : finrank ℝ (P j).seed.covector.ker + 1 = finrank ℝ E := by
    simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using
      (P j).seed.normalization.toLinearEquiv.finrank_eq
  have hqdim : finrank ℝ (P j).seed.covector.ker = finrank ℝ E - 1 := by omega
  have hnormalizationJ (n : ℕ) : scale n ^ finrank ℝ (P j).seed.covector.ker = (n : ℝ) + 1 := by
    simpa only [hqdim] using hnormalization n
  obtain ⟨φ, hφ, ψ, hψ, hgap⟩ :=
    exists_original_seed_macro_clock_probe_gap_curry_zero_refining_of_face j
      hF hcomplete hu ha hinj horder hdim m hμchart hνchart nearRadius
      scale hscalePos hscale hnormalizationJ probe hprobe G hprobeBound t ht0 ht0lim
      ap am hpm hmm hp hm hμlaw hνlaw hAsupport hBsupport hAB hμreg hνreg
      hκ hbalance hcore hrecovery hface hμA hνB hnearRadius Energy hEnergy hEp hEm
      φ₀ hφ₀ ψ₀ hψ₀
  refine ⟨fun ℓ n ↦ laws ℓ (φ₀ ℓ (φ ℓ n)), Q, fun ℓ ↦ ψ₀ (ψ ℓ), ?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ
    exact (hinner ℓ).comp (hφ ℓ).tendsto_atTop
  · exact houter.comp hψ.tendsto_atTop
  · intro ℓ n
    exact (hsource ℓ (φ₀ ℓ (φ ℓ n))).mono fun s hs ↦ hs.1
  · intro ℓ n
    exact (hsource ℓ (φ₀ ℓ (φ ℓ n))).mono fun s hs ↦ hs.2
  · intro g
    apply (hgap g).congr'
    apply Eventually.of_forall
    intro p
    have heq := lintegral_originalAllocationPlanPairLaw_seed_probe_eq_restrict_readout
      (P := P) (a := a) (κ := κ) (lambda := μ.map a) hF hcomplete hu ha hinj
      (Penv (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2))) μ ν
      (ap (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2)))
      (am (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2)))
      (hpm (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2)))
      (hmm (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2)))
      (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst) (fun w ↦ w.2)
      (hfp (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2)))
      (hfm (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2))) j g
    simpa only [physicalSceneOriginalSeedPairReadout] using heq.symm

end OTSelector.Reconstruction

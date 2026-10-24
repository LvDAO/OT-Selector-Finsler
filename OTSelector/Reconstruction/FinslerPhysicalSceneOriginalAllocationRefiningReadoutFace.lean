import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationLimitAgreement
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalDirichletFaceEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationOptimalRefining
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationContinuousReadout
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationProbeLaw
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalIteratedProbeAgreement
import OTSelector.Probability.ProbabilityMeasureWeakSecondCountable

/-!
# Original populations refine every prescribed pair of sample and tilt indices

Actual original compact populations produce the two weak stages after every
prescribed pair of strict subsequences. Their original Dirichlet energy and
optimality are produced internally, and complete continuous readouts vanish.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction
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


/-- Every prescribed original sample and tilt subsequence has a further refinement
with vanishing complete bounded continuous probe gaps. The two original weak laws,
energy, optimality, and agreement are all produced internally. -/
theorem exists_refining_originalAllocation_continuous_probe_gap_curry_zero_of_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hdim : 6 ≤ Module.finrank ℝ E) (m : Measure E) [m.IsAddHaarMeasure]
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
    (φ₀ : ℕ → ℕ → ℕ) (hφ₀ : ∀ ℓ, StrictMono (φ₀ ℓ))
    (ψ₀ : ℕ → ℕ) (hψ₀ : StrictMono ψ₀)
    :
    let _inst : MetricSpace M := F.metricSpace
    ∃ φ : ℕ → ℕ → ℕ, (∀ ℓ, StrictMono (φ ℓ)) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ f : (M × M) →ᵇ ℝ,
      Tendsto (fun z : ℕ × ℕ ↦ ∫ w,
        |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ
            (ap (ψ₀ (ψ z.1)) (φ₀ (ψ₀ (ψ z.1)) (φ (ψ₀ (ψ z.1)) z.2))) (fun w ↦ w.1) w) -
          ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ
            (am (ψ₀ (ψ z.1)) (φ₀ (ψ₀ (ψ z.1)) (φ (ψ₀ (ψ z.1)) z.2))) (fun w ↦ w.1) w|
        ∂((Measure.pi (fun _ : Fin (φ₀ (ψ₀ (ψ z.1)) (φ (ψ₀ (ψ z.1)) z.2) + 1) ↦ ν)).prod
          (dirichletOne (φ₀ (ψ₀ (ψ z.1)) (φ (ψ₀ (ψ z.1)) z.2)))))
        ((atTop : Filter ℕ).curry atTop) (𝓝 0) ∧
      Tendsto (fun z : ℕ × ℕ ↦ ∫⁻ w, ENNReal.ofReal
        |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ
            (ap (ψ₀ (ψ z.1)) (φ₀ (ψ₀ (ψ z.1)) (φ (ψ₀ (ψ z.1)) z.2))) (fun w ↦ w.1) w) -
          ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ
            (am (ψ₀ (ψ z.1)) (φ₀ (ψ₀ (ψ z.1)) (φ (ψ₀ (ψ z.1)) z.2))) (fun w ↦ w.1) w|
        ∂((Measure.pi (fun _ : Fin (φ₀ (ψ₀ (ψ z.1)) (φ (ψ₀ (ψ z.1)) z.2) + 1) ↦ ν)).prod
          (dirichletOne (φ₀ (ψ₀ (ψ z.1)) (φ (ψ₀ (ψ z.1)) z.2)))))
        ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  let _instPlanBorel : BorelSpace (ProbabilityMeasure (M × M)) := probabilityMeasure_weakBorelSpace
  let _instPlanSecond : SecondCountableTopology (ProbabilityMeasure (M × M)) :=
    probabilityMeasure_weakSecondCountable
  let Penv := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let laws := fun ℓ n ↦ physicalSceneOriginalAllocationPlanPairLaw (Penv n) μ ν
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
    (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
  dsimp only
  have hdimKer : finrank ℝ (P 0).seed.covector.ker + 1 = finrank ℝ E := by
    simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using
      (P 0).seed.normalization.toLinearEquiv.finrank_eq
  have hqdim : finrank ℝ (P 0).seed.covector.ker = finrank ℝ E - 1 := by omega
  have hnormalizationJ (n : ℕ) : scale n ^ finrank ℝ (P 0).seed.covector.ker = (n : ℝ) + 1 := by
    simpa only [hqdim] using hnormalization n
  obtain ⟨Energy, hEnergy, hconsume⟩ := exists_original_global_dirichlet_allocation_energy_of_face
    hF hcomplete hdim hu ha hinj horder m hμchart hνchart hAsupport hBsupport hAB
    (ae_iff.mpr hμA) (ae_iff.mpr hνB) hμreg hνreg hface
    (P 0) scale hscalePos hnormalizationJ probe hprobe G hprobeBound t ht0lim
  have hEp ℓ n := hconsume ℓ n (t ℓ) (Or.inl rfl) (ap ℓ n) (hpm ℓ n) (hp ℓ n)
  have hEm ℓ n := hconsume ℓ n (-t ℓ) (Or.inr rfl) (am ℓ n) (hmm ℓ n) (hm ℓ n)
  have hfp (ℓ n : ℕ) : ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ w.2 (ap ℓ n w) :=
    (hp ℓ n).mono fun _ hw ↦ hw.1
  have hfm (ℓ n : ℕ) : ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ w.2 (am ℓ n w) :=
    (hm ℓ n).mono fun _ hw ↦ hw.1
  obtain ⟨Q, φ, hφ, hinner, _hQopt, R, ψ, hψ, houter, hRopt⟩ :=
    exists_refining_iterated_optimal_originalAllocationPlanPairLaw
      μ ν u hu a ha (F.potentialRegularDomain u)
      (hF.measurableSet_potentialRegularDomain hcomplete u) hμreg hνreg horder hface
      ap am hpm hmm hfp hfm hAsupport hBsupport (ae_iff.mpr hμA) (ae_iff.mpr hνB)
      scale hscalePos hscale hEnergy hEp hEm φ₀ hφ₀ ψ₀ hψ₀
  have hφall (ℓ : ℕ) : StrictMono (fun n ↦ φ₀ ℓ (φ ℓ n)) := (hφ₀ ℓ).comp (hφ ℓ)
  have hψall : StrictMono (fun ℓ ↦ ψ₀ (ψ ℓ)) := hψ₀.comp hψ
  have hdiag := ae_originalAllocationPlanPairLaw_eq_of_iterated_limits_of_face
    hF hcomplete hu ha hinj horder (by omega) m hμchart hνchart nearRadius
    scale hscalePos hscale hnormalization probe hprobe G hprobeBound t ht0 ht0lim
    ap am hpm hmm hp hm hμlaw hνlaw hAsupport hBsupport hAB hμreg hνreg
    hκ hbalance hcore hrecovery hface hμA hνB hnearRadius Energy hEnergy hEp hEm
    (fun ℓ n ↦ φ₀ ℓ (φ ℓ n)) hφall (fun ℓ ↦ ψ₀ (ψ ℓ)) hψall
    Q R hinner houter (hRopt.mono fun _ h ↦ h.1) (hRopt.mono fun _ h ↦ h.2)
  refine ⟨φ, hφ, ψ, hψ, ?_⟩
  intro f
  have hr := tendsto_originalAllocation_continuous_probe_gap_curry_zero_of_iterated_diagonal
    Penv μ ν ap am hpm hmm (fun _ w ↦ w.1)
    (fun _ k ↦ (measurable_pi_apply k).comp measurable_fst) (fun _ w ↦ w.2)
    hfp hfm (fun ℓ n ↦ φ₀ ℓ (φ ℓ n)) (fun ℓ ↦ ψ₀ (ψ ℓ))
    Q R hinner houter hdiag f
  exact ⟨hr.2.1, hr.2.2⟩

end OTSelector.Reconstruction

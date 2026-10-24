import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationLimitAgreement
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalDirichletFaceEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationRefiningReadoutFace
import OTSelector.Topology.CurriedSubsequenceCriterion
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationContinuousReadout
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationProbeLaw
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalIteratedProbeAgreement
import OTSelector.Probability.ProbabilityMeasureWeakSecondCountable

/-!
# Complete original continuous readouts vanish without extracted weak laws

Actual original populations produce two optimal weak stages after every pair
of prescribed strict subsequences. Agreement at those same original laws and
the two-index subsequence criterion yield convergence of the entire family.
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


/-- Every complete bounded continuous original endpoint probe has vanishing real
and extended expected absolute gap for the full original allocation family. The
weak laws, energy, optimality, agreement and subsequence extraction are internal. -/
theorem tendsto_originalAllocation_continuous_probe_gap_curry_zero_of_original_face
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
    :
    let _inst : MetricSpace M := F.metricSpace
    ∀ f : (M × M) →ᵇ ℝ,
      (∀ ℓ n, Integrable (fun w ↦
        |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1) w) -
          ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1) w|)
        ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ∧
      Tendsto (fun z : ℕ × ℕ ↦ ∫ w,
        |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (ap z.1 z.2) (fun w ↦ w.1) w) -
          ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (am z.1 z.2) (fun w ↦ w.1) w|
        ∂((Measure.pi (fun _ : Fin (z.2 + 1) ↦ ν)).prod (dirichletOne z.2)))
        ((atTop : Filter ℕ).curry atTop) (𝓝 0) ∧
      Tendsto (fun z : ℕ × ℕ ↦ ∫⁻ w, ENNReal.ofReal
        |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (ap z.1 z.2) (fun w ↦ w.1) w) -
          ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (am z.1 z.2) (fun w ↦ w.1) w|
        ∂((Measure.pi (fun _ : Fin (z.2 + 1) ↦ ν)).prod (dirichletOne z.2)))
        ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  dsimp only
  intro f
  let Penv := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let gap := fun ℓ n w ↦
    |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1) w) -
      ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1) w|
  let A := fun ℓ n ↦ ∫ w, gap ℓ n w ∂Penv n
  let B := fun ℓ n ↦ ∫⁻ w, ENNReal.ofReal (gap ℓ n w) ∂Penv n
  have hwhole : Tendsto (fun z : ℕ × ℕ ↦ (A z.1 z.2, B z.1 z.2))
      ((atTop : Filter ℕ).curry atTop) (𝓝 (0 : ℝ × ℝ≥0∞)) := by
    apply tendsto_curry_zero_of_forall_strictMono_subsequence_has_refinement
      (fun ℓ n ↦ (A ℓ n, B ℓ n))
    intro ψ₀ hψ₀ φ₀ hφ₀
    obtain ⟨φ, hφ, ψ, hψ, hgap⟩ :=
      exists_refining_originalAllocation_continuous_probe_gap_curry_zero_of_face
        hF hcomplete hu ha hinj horder hdim m hμchart hνchart nearRadius
        scale hscalePos hscale hnormalization probe hprobe G hprobeBound t ht0 ht0lim
        ap am hpm hmm hp hm hμlaw hνlaw hAsupport hBsupport hAB hμreg hνreg
        hκ hbalance hcore hrecovery hface hμA hνB hnearRadius φ₀ hφ₀ ψ₀ hψ₀
    refine ⟨ψ, hψ, (fun ℓ ↦ φ (ψ₀ (ψ ℓ))), (fun ℓ ↦ hφ (ψ₀ (ψ ℓ))), ?_⟩
    exact (hgap f).1.prodMk_nhds (hgap f).2
  refine ⟨?_, (continuous_fst.tendsto (0 : ℝ × ℝ≥0∞)).comp hwhole,
    (continuous_snd.tendsto (0 : ℝ × ℝ≥0∞)).comp hwhole⟩
  intro ℓ n
  exact integrable_originalAllocation_continuous_probe_gap (Penv n) μ ν
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (fun w ↦ w.1)
    (fun k ↦ (measurable_pi_apply k).comp measurable_fst) (fun w ↦ w.2)
    ((hp ℓ n).mono fun _ hw ↦ hw.1) ((hm ℓ n).mono fun _ hw ↦ hw.1) f

end OTSelector.Reconstruction

import OTSelector.Reconstruction.FinslerConcreteUpperOriginalDirichletFaceEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedProbeGapRefinement

/-! Original seed probes recover from actual original optimal allocations,
with their finite Dirichlet energy produced internally. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
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


variable (j : ℕ)

/-- Every prescribed original sample/tilt subsequence admits a further common
refinement recovering all compact seed probes. Its physical allocation energy
is derived from the unchanged whole optimal face and original populations. -/
theorem exists_original_seed_probe_gap_refining_of_original_energy
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
    (hnormalization : ∀ n, scale n ^ finrank ℝ (P j).seed.covector.ker = (n : ℝ) + 1)
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
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let Γp := fun ℓ n w ↦ (physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1) w).restrict (H ×ˢ univ)
    let Γm := fun ℓ n w ↦ (physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1) w).restrict (H ×ˢ univ)
    ∃ φ : ℕ → ℕ → ℕ, (∀ ℓ, StrictMono (φ ℓ)) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ),
          Tendsto (fun p : ℕ × ℕ ↦ ∫⁻ w, ENNReal.ofReal
            |(∫ e, g (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j e.1,
                  (u e.1, u e.2)) ∂Γp (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2)) w) -
              ∫ e, g (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j e.1,
                  (u e.1, u e.2)) ∂Γm (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2)) w|
            ∂((Measure.pi (fun _ : Fin (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2) + 1) ↦ ν)).prod
              (dirichletOne (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2)))))
            ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  have hμcarried : ∀ᵐ x ∂μ, x ∈ A := ae_iff.mpr hμA
  have hνcarried : ∀ᵐ y ∂ν, y ∈ B := ae_iff.mpr hνB
  obtain ⟨Energy,hEnergy,hconsume⟩ := exists_original_global_dirichlet_allocation_energy_of_face
    hF hcomplete hdim hu ha hinj horder m hμchart hνchart hAsupport hBsupport hAB
    hμcarried hνcarried hμreg hνreg hface (P j) scale hscalePos hnormalization
    probe hprobe G hprobeBound t ht0lim
  have hEp ℓ n := hconsume ℓ n (t ℓ) (Or.inl rfl) (ap ℓ n) (hpm ℓ n) (hp ℓ n)
  have hEm ℓ n := hconsume ℓ n (-t ℓ) (Or.inr rfl) (am ℓ n) (hmm ℓ n) (hm ℓ n)
  exact exists_original_seed_macro_clock_probe_gap_curry_zero_refining_of_face j
    hF hcomplete hu ha hinj horder (by omega) m hμchart hνchart nearRadius
    scale hscalePos hscale hnormalization probe hprobe G hprobeBound t ht0 ht0lim
    ap am hpm hmm hp hm hμlaw hνlaw hAsupport hBsupport hAB hμreg hνreg
    hκ hbalance hcore hrecovery hface hμA hνB hnearRadius Energy hEnergy hEp hEm
    φ₀ hφ₀ ψ₀ hψ₀

end OTSelector.Reconstruction

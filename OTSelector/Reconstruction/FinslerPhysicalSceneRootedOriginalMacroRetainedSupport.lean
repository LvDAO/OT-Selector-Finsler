import OTSelector.Transport.CyclicMonotonicity.TaggedCycleSupport
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMacroTagRetained
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalTaylorRetainedLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedWeightedCoreWitness

/-!
# Actual retained support cycles at the original varying macroscopic coefficient

Original Taylor control and finite core isolation give local packing witnesses.
Both original weak stages and a countable macro basis put their consequences
on one probability-one event for the SAME actual joint scene. The resulting
cost depends on the actual macro tag and is independent of auxiliary core data.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
  OTSelector.Probability TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
  (i : Fin D.haar.continuous.count)
variable (base : ((D.coreSpatialCoordinateSpace i) × ℝ))


local instance originalMacroRetainedSupportStandardBorel :
    StandardBorelSpace ((D.coreSpatialCoordinateSpace i) × ℝ) := inferInstance
local instance originalMacroRetainedSupportConfigTopology :
    TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance originalMacroRetainedSupportConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace (base := base)
local instance originalMacroRetainedSupportConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace (base := base)
local instance originalMacroRetainedSupportPlanPolish : PolishSpace
    (LocalFiniteMeasure (((D.coreSpatialCoordinateSpace i) × ℝ) ×
      ((D.coreSpatialCoordinateSpace i) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

local notation "MacroScene" => (D.coreSpatialCoordinateSpace i) ×
  (CavityLocalScene ((D.coreSpatialCoordinateSpace i) × ℝ)
    ((D.coreSpatialCoordinateSpace i) × ℝ) × LocalConfiguration base)

local notation "JointScene" => MacroScene ×
  (CavityLocalScene ((D.coreSpatialCoordinateSpace i) × ℝ)
    ((D.coreSpatialCoordinateSpace i) × ℝ) ×
   CavityLocalScene ((D.coreSpatialCoordinateSpace i) × ℝ)
    ((D.coreSpatialCoordinateSpace i) × ℝ))

/-- Original global opposite optimizers, original Taylor control and finite
core isolation produce one common AE no-cycle statement for the retained average
at the SAME original macro-tag coefficient. No local witness oracle is assumed. -/
theorem ae_original_macro_tag_retained_support_twoCycle
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
    {Acompact A B : Set M}
    (hAcompact : IsCompact Acompact) (hμAcompact : ∀ᵐ x ∂μ, x ∈ Acompact)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAreg : A ⊆ F.potentialRegularDomain u) (hBreg : B ⊆ F.potentialRegularDomain u)
    (nearRadius : ℝ)
    (R sL sR tL tR : ℝ)
    (hs : Icc sL sR ⊆ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
      ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ))
    (ht : Icc tL tR ⊆ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
      ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ))
    (hclockgap : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ tL - sR)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
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
    (rootDomain : ℕ → Set (D.coreSpatialCoordinateSpace i))
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1)) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D.haar.continuous.coefficient i).seedIndex
    let laws := fun ℓ n ↦ actualAllocationRootedMaskedMacroscopicSceneLaw base
      ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
      (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
      (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
      H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj _)
      (D.retainedNearCarrierEvent A B nearRadius)
      (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
      (physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex (scale n))
      (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ (scale n))
      u (by
        let _inst : MetricSpace M := F.metricSpace
        exact hu.continuous.measurable) (scale n) (rootDomain n) (hrootDomain n)
    ∀ (Q : ℕ → ProbabilityMeasure JointScene) (Rlaw : ProbabilityMeasure JointScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) →
      ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop →
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 Rlaw) →
      ∀ᵐ s ∂(Rlaw : Measure JointScene),
        s.1.1 ∈ physicalSceneOriginalMacroLabel (P := P) (a := a)
            (D.haar.continuous.coefficient i).seedIndex '' (D.haar.continuous.coefficient i).roots →
        IsTwoCycleMonotoneOn
          (physicalSceneOriginalMacroCost (P := P) (a := a)
            (D.haar.continuous.coefficient i).seedIndex s.1.1)
          ((D.haar.continuous.coefficient i).frozenClockRadiusOpenRectangle R sL sR tL tR)
          (((LocalFiniteMeasure.cavityAverage s.2.1 : Measure _).support) ∩
            (D.haar.continuous.coefficient i).frozenClockRadiusOpenRectangle R sL sR tL tR) := by
  let _inst : MetricSpace M := F.metricSpace
  dsimp only
  intro Q Rlaw φ hφ ψ hψ hinner houter
  let C := D.haar.continuous.coefficient i
  let K := physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' C.roots
  let cost := physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex
  let legal := C.frozenClockRadiusOpenRectangle R sL sR tL tR
  apply ae_tagged_legal_twoCycle_support_of_local_zero_witnesses
    (Rlaw : Measure JointScene) (fun s ↦ s.1.1)
    (fun s ↦ (LocalFiniteMeasure.cavityAverage s.2.1 : Measure _)) K cost (fun _ ↦ legal)
    isTopologicalBasis_cavitySpatialBasis isTopologicalBasis_cavitySpatialBasis
    countable_cavitySpatialBasis countable_cavitySpatialBasis
  rintro w ⟨macroCenter, hmacroCenter, rfl⟩ x y x' y' hxy hxy' hcross hcross' hbad
  let w := physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex macroCenter
  let γ := (cost w x y + cost w x' y' - cost w x y' - cost w x' y) / 4
  have hγ : 0 < γ := by dsimp only [γ]; linarith
  obtain ⟨ε, hε, T, Acert, macroRadius, hmacroRadius, threshold, _hthreshold, hcert⟩ :=
    D.exists_original_macro_tag_taylor_retained_witness_budget i base
      hF hcomplete hu ha hinj horder hdim m hμchart hνchart hAcompact hμAcompact
      hA hB hAreg hBreg nearRadius hmacroCenter R sL sR tL tR hs ht hclockgap γ hγ
  let ξ : Fin 2 → ((D.coreSpatialCoordinateSpace i) × ℝ) := ![x, x']
  let η : Fin 2 → ((D.coreSpatialCoordinateSpace i) × ℝ) := ![y, y']
  have hξR (k : Fin 2) : ‖(ξ k).1‖ < R := by
    fin_cases k
    · exact hxy.2.1
    · exact hxy'.2.1
  have hηR (k : Fin 2) : ‖(η k).1‖ < R := by
    fin_cases k
    · exact hxy.2.2
    · exact hxy'.2.2
  have hξclock (k : Fin 2) : (ξ k).2 ∈ Ioo sL sR := by
    fin_cases k
    · exact hxy.1.1
    · exact hxy'.1.1
  have hηclock (k : Fin 2) : (η k).2 ∈ Ioo tL tR := by
    fin_cases k
    · exact hxy.1.2
    · exact hxy'.1.2
  have hcycle : 2 * γ < cost w (ξ 0) (η 0) + cost w (ξ 1) (η 1) -
      cost w (ξ 0) (η 1) - cost w (ξ 1) (η 0) := by
    simp only [ξ, η, Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp only [γ]
    linarith
  obtain ⟨idx, _hidxgap, _hlegal, hleft, hright, phaseSize, _hphase, _offset, _hbox, hbudget⟩ :=
    hcert ξ η hξR hηR hξclock hηclock hcycle
  let U := Metric.ball (D.coreMacroLabel i macroCenter) macroRadius
  have hzero := OriginalFixedSeedMacroRetainedRectangleBudget.ae_zero_of_iterated_actual_scene
    D i base hF hcomplete hu ha hinj A B hA hB nearRadius threshold (γ / 2) phaseSize
    (half_pos hγ) U Metric.isOpen_ball
    idx.1.1.1.val idx.1.2.1.val idx.1.1.2.val idx.1.2.2.val
    (isTopologicalBasis_cavitySpatialBasis.isOpen idx.1.1.1.property)
    (isTopologicalBasis_cavitySpatialBasis.isOpen idx.1.2.1.property)
    (isTopologicalBasis_cavitySpatialBasis.isOpen idx.1.1.2.property)
    (isTopologicalBasis_cavitySpatialBasis.isOpen idx.1.2.2.property)
    hbudget scale hscale probe hprobe G hprobeBound t ht0 ht0lim ap am hpm hmm hp hm
    rootDomain hrootDomain Q Rlaw φ hφ ψ hψ hinner houter
  refine ⟨U, Metric.isOpen_ball, ?_, idx, ?_, ?_, ?_⟩
  · exact Metric.mem_ball_self hmacroRadius
  · simpa only [ξ, η, Matrix.cons_val_zero] using hleft
  · simpa only [ξ, η, Matrix.cons_val_one, Matrix.cons_val_zero] using hright
  · filter_upwards [hzero] with s hs hsU
    simpa only [physicalSceneMaskedRetainedAverageWitness, Set.indicator_of_mem hsU,
      cavityBasisCycleWitness] using hs

end PopulationLocalPressureCore
end OTSelector.Reconstruction

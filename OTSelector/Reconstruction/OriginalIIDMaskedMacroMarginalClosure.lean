import OTSelector.Reconstruction.OriginalIIDMaskedBipartiteMacroScene
import OTSelector.Reconstruction.OriginalIIDFixedSeedTargetDefect
import OTSelector.Reconstruction.OriginalIIDMaskedMacroInputJointLaw
import OTSelector.MeasureTheory.WeakInputMarginalsCompactTail
import OTSelector.Reconstruction.OriginalIIDFixedSeedCompactPartnerTails
import OTSelector.Reconstruction.OriginalIIDMaskedMacroTailReadout
import OTSelector.Reconstruction.OriginalIIDSupportedSpatialEnergy

/-!
# Actual masked macro-scene marginal closure

The finite source input is the literal source marginal of the same original
optimizer, after the fixed source mask and the actual root translation.
The target input remains the same independently sampled masked second array.
Actual finite target-defect estimates and compact partner tails recover both
complete marginals on every genuine weak subsequential macro law. The supported
pressure-data corollary derives its true energy budget internally.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
  Manifold Module OTSelector.Geometry
open scoped CompactlySupported BoundedContinuousFunction BigOperators ENNReal ContDiff

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false

section LiteralCounting
variable {Ω X : Type*} [MeasurableSpace Ω] [MetricSpace X] [MeasurableSpace X]

/-- The retained original tuple is exactly the sample-size rescaling of the
same masked empirical law, including every repeated observation. -/
theorem countingMeasure_ofMaskedTuple_eq_scaled_empirical
    {N : ℕ} [NeZero N] (base : X) {H : Set Ω} (hH : MeasurableSet H)
    {obs : Ω → X} (hobs : Measurable obs) (sample : Fin N → Ω) :
    LocalConfiguration.countingMeasure (LocalConfiguration.ofMaskedTuple base H obs sample) =
      (N : ℝ≥0∞) • ((empiricalMeasure sample).restrict H).map obs := by
  classical
  ext U hU
  have hpre : MeasurableSet (obs ⁻¹' U ∩ H) := (hU.preimage hobs).inter hH
  rw [LocalConfiguration.countingMeasure_ofMaskedTuple, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.map_apply hobs hU,
    Measure.restrict_apply (hU.preimage hobs)]
  simp only [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne N) (by simp), one_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : sample j ∈ H
  · simp [hj, Measure.dirac_apply' _ hU, Measure.dirac_apply' _ hpre, Set.indicator_apply]
  · simp [hj, Measure.dirac_apply' _ hpre]

end LiteralCounting

section RootedSource
variable {M ι : Type*} [MeasurableSpace M] [Fintype ι]

/-- The rooted source-restricted actual iid optimizer has exactly its original
H-masked source counting measure when the root mass is the sample size. -/
theorem originalIID_rooted_source_restriction_fst_eq_masked_countingMeasure
    (base : (ι → ℝ) × ℝ) (cost : M → M → ℝ) (selectionScale : ℝ) (n : ℕ)
    (ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M)) {H : Set M} (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (z : ι → ℝ) :
    (physicalSceneRootedPlan
      ((originalIIDOptimalPhysicalPlan cost selectionScale ξ).restrict (H ×ˢ univ))
      coord u ((n : ℝ) + 1) z).fst =
        LocalConfiguration.countingMeasure (LocalConfiguration.ofMaskedTuple base H
          (fun x ↦ (coord x - z, u x)) ξ.1) := by
  let Γ := originalIIDOptimalPhysicalPlan cost selectionScale ξ
  let endpoint := fun x : M ↦ (coord x - z, u x)
  have he : Measurable endpoint := (hcoord.sub measurable_const).prodMk hu
  have hm := (physicalSceneRootedPlan_marginals (Γ.restrict (H ×ˢ univ))
    coord hcoord u hu ((n : ℝ) + 1) z).1
  rw [fst_actual_source_restriction Γ H hH,
    show Γ.fst = empiricalMeasure ξ.1 from
      originalIIDOptimalPhysicalPlan_source cost selectionScale ξ] at hm
  rw [hm, countingMeasure_ofMaskedTuple_eq_scaled_empirical base hH he]
  simp only [Nat.cast_add, Nat.cast_one, ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one,
    ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rfl

/-- Every compact source readout agrees pointwise with the same original masked
first array. Its finite expected source defect is therefore literally zero. -/
theorem integral_originalIID_rooted_source_eq_literal_masked_input
    (base : (ι → ℝ) × ℝ) (cost : M → M → ℝ) (selectionScale : ℝ) (n : ℕ)
    (ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M)) {H : Set M} (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (z : ι → ℝ)
    (f : C_c((ι → ℝ) × ℝ, ℝ)) :
    LocalConfiguration.testIntegral
      (LocalConfiguration.ofMaskedTuple base H (fun x ↦ (coord x - z, u x)) ξ.1) f =
      ∫ e, f e.1 ∂physicalSceneRootedPlan
        ((originalIIDOptimalPhysicalPlan cost selectionScale ξ).restrict (H ×ˢ univ))
        coord u ((n : ℝ) + 1) z := by
  rw [← LocalConfiguration.integral_countingMeasure]
  rw [← originalIID_rooted_source_restriction_fst_eq_masked_countingMeasure
    base cost selectionScale n ξ hH coord hcoord u hu z]
  exact integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable

end RootedSource

section ActualFiniteLaw
variable {M ι : Type*} [MeasurableSpace M] [Fintype ι]
variable (base : (ι → ℝ) × ℝ)
local instance maskedMacroMarginalClosureInst1 : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance maskedMacroMarginalClosureInst2 : TopologicalSpace (LocalConfiguration base) := LocalConfiguration.vagueTopology base
local instance maskedMacroMarginalClosureInst3 : BorelSpace (LocalConfiguration base) := LocalConfiguration.vagueBorelSpace
local instance maskedMacroMarginalClosureInst4 : PolishSpace (LocalConfiguration base) := LocalConfiguration.vaguePolishSpace
local instance maskedMacroMarginalClosureInst5 : PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
set_option quotPrecheck false
local notation "Pt" => (ι → ℝ) × ℝ
local notation "PairScene" => CavityLocalScene Pt Pt
local notation "Macro" => (ι → ℝ) × (PairScene × LocalConfiguration base)

/-- Under the actual original iid/Haar-rooted macro law the full source test
error is zero at every finite index, with the literal original masked input. -/
theorem lintegral_originalIIDMaskedMacroLaw_source_test_error_eq_zero
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι) (cost : M → M → ℝ)
    (hcost : Measurable (Function.uncurry cost)) (k : ℝ) (n : ℕ)
    {H : Set M} (hH : MeasurableSet H)
    {coord : M → (ι → ℝ)} (hcoord : Measurable coord)
    {u : M → ℝ} (hu : Measurable u) (f : C_c(Pt, ℝ)) :
    (∫⁻ s : Macro × Macro, ENNReal.ofReal
      |LocalFiniteMeasure.testIntegral
        (originalIIDMaskedMacroInputProjection base s).1 f -
        ∫ e, f e.1 ∂(s.1.2.1.1 : Measure (Pt × Pt))|
      ∂(originalIIDMaskedBipartiteMacroLaw base μ ν hq cost hcost k n H hH
        coord hcoord u hu : Measure (Macro × Macro))) = 0 := by
  apply le_antisymm ?_ zero_le
  change (∫⁻ s, _ ∂Measure.map _ _) ≤ 0
  refine (lintegral_map_le _ _).trans ?_
  have hz : ∀ w : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) × (ι → ℝ),
      ENNReal.ofReal
      |LocalFiniteMeasure.testIntegral
        (originalIIDMaskedMacroInputProjection base
          (originalIIDMaskedBipartiteMacroObservation base cost k n H coord u
            (2 * haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)) w)).1 f -
        ∫ e, f e.1 ∂((originalIIDMaskedBipartiteMacroObservation base cost k n H coord u
          (2 * haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)) w).1.2.1.1 :
          Measure (Pt × Pt))| = 0 := by
    intro w
    change ENNReal.ofReal
      |LocalFiniteMeasure.testIntegral
        (LocalConfiguration.toLocalFiniteMeasure (LocalConfiguration.ofMaskedTuple base H (fun x ↦ (coord x - w.2, u x)) w.1.1)) f -
        ∫ e, f e.1 ∂physicalSceneRootedPlan
          ((originalIIDOptimalPhysicalPlan cost k w.1).restrict (H ×ˢ univ))
          coord u ((n : ℝ) + 1) w.2| = 0
    rw [LocalConfiguration.testIntegral_toLocalFiniteMeasure,
      integral_originalIID_rooted_source_eq_literal_masked_input
      base cost k n w.1 hH coord hcoord u hu w.2 f]
    simp
  simpa only [hz, lintegral_zero] using (le_rfl : (0 : ℝ≥0∞) ≤ 0)

/-- The actual macro-law target discrepancy is bounded by the literal second
array discrepancy in the same raw iid experiment and Haar root law. -/
theorem lintegral_originalIIDMaskedMacroLaw_target_test_error_le
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι) (cost : M → M → ℝ)
    (hcost : Measurable (Function.uncurry cost)) (k : ℝ) (n : ℕ)
    {H : Set M} (hH : MeasurableSet H)
    {coord : M → (ι → ℝ)} (hcoord : Measurable coord)
    {u : M → ℝ} (hu : Measurable u) (f : C_c(Pt, ℝ)) :
    (∫⁻ s : Macro × Macro, ENNReal.ofReal
      |LocalFiniteMeasure.testIntegral
        (originalIIDMaskedMacroInputProjection base s).2 f -
        ∫ e, f e.2 ∂(s.1.2.1.1 : Measure (Pt × Pt))|
      ∂(originalIIDMaskedBipartiteMacroLaw base μ ν hq cost hcost k n H hH
        coord hcoord u hu : Measure (Macro × Macro))) ≤
      ∫⁻ ξ, ∫⁻ z, ENNReal.ofReal
        |(∫ e, f e.2 ∂physicalSceneRootedPlan
          ((originalIIDOptimalPhysicalPlan cost k ξ).restrict (H ×ˢ univ))
          coord u ((n : ℝ) + 1) z) -
          ∑ i, H.indicator (fun y ↦ f (coord y - z, u y)) (ξ.2 i)|
        ∂cavityRootMeasure volume
          (haarRootCube ι (haarRootRadius (Fintype.card ι) ((n : ℝ) + 1))) ((n : ℝ) + 1)
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν)) := by
  change (∫⁻ s, _ ∂Measure.map _ _) ≤ _
  refine (lintegral_map_le _ _).trans ?_
  refine (lintegral_prod_le _).trans_eq ?_
  apply lintegral_congr
  intro ξ
  apply lintegral_congr
  intro z
  change ENNReal.ofReal
    |LocalFiniteMeasure.testIntegral
      (LocalConfiguration.toLocalFiniteMeasure (LocalConfiguration.ofMaskedTuple base H (fun x ↦ (coord x - z, u x)) ξ.2)) f -
      ∫ e, f e.2 ∂physicalSceneRootedPlan
        ((originalIIDOptimalPhysicalPlan cost k ξ).restrict (H ×ˢ univ))
        coord u ((n : ℝ) + 1) z| = _
  rw [LocalConfiguration.testIntegral_toLocalFiniteMeasure,
    LocalConfiguration.testIntegral_ofMaskedTuple, abs_sub_comm]


end ActualFiniteLaw
section FinslerClosure
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

variable
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
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (selectionScale spatialScale : ℕ → ℝ) (hsp : ∀ n, 0 < spatialScale n)
    (hscale : Tendsto (fun n ↦ spatialScale n ^ 2) atTop atTop)

variable (j : ℕ)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂originalIIDOptimalPhysicalPlan (cost n) (selectionScale n) ξ
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) ≤ C)

variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local instance maskedMacroMarginalClosureInst6 : StandardBorelSpace ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) := inferInstance
local instance maskedMacroMarginalClosureInst7 : TopologicalSpace (LocalConfiguration base) := LocalConfiguration.vagueTopology base
local instance maskedMacroMarginalClosureInst8 : BorelSpace (LocalConfiguration base) := LocalConfiguration.vagueBorelSpace
local instance maskedMacroMarginalClosureInst9 : PolishSpace (LocalConfiguration base) := LocalConfiguration.vaguePolishSpace
local instance maskedMacroMarginalClosureInst10 : PolishSpace (LocalFiniteMeasure
    (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ×
      ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
set_option quotPrecheck false
local notation "Pt" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ
local notation "Macro" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) ×
  (CavityLocalScene Pt Pt × LocalConfiguration base)

include hcore hrecovery hκ horder hbalance hA hB hμ hν hreg hμreg hface hgap hdist
  hsp hscale hC henergy

/-- Any genuine weak subsequential law of the actual full-seed masked optimizer
has both complete marginals equal to its same two original retained inputs. -/
theorem ae_originalIID_fixed_seed_masked_macro_input_marginals
    (hq : 0 < finrank ℝ (P j).seed.covector.ker)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (Q : ProbabilityMeasure (Macro × Macro))
    (hweak : Tendsto (fun n ↦
      originalIIDMaskedBipartiteMacroLaw base μ ν (by simpa using hq)
        (cost (φ n)) (hcost (φ n)) (selectionScale (φ n)) (φ n)
        (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j)
        (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
        (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale (φ n)))
        (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j
          (spatialScale (φ n)))
        u (by let _inst : MetricSpace M := F.metricSpace; exact hu.continuous.measurable))
        atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (Macro × Macro)),
      (originalIIDMaskedMacroPlan base s : Measure (Pt × Pt)).fst =
        (originalIIDMaskedMacroInputProjection base s).1 ∧
      (originalIIDMaskedMacroPlan base s : Measure (Pt × Pt)).snd =
        (originalIIDMaskedMacroInputProjection base s).2 := by
  let _inst : MetricSpace M := F.metricSpace
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition
    (P := P) (a := a) j (spatialScale n)
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (spatialScale n)
  have hum : Measurable u := hu.continuous.measurable
  have hqdim : 0 < Fintype.card (Fin (finrank ℝ (P j).seed.covector.ker)) := by simpa using hq
  let laws := fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν hqdim
    (cost n) (hcost n) (selectionScale n) n H hH (coord n) (hcoord n) u hum
  let rootMass : ℕ → ℝ := fun n ↦ (n : ℝ) + 1
  let rootDomain := fun n ↦ haarRootCube (Fin (finrank ℝ (P j).seed.covector.ker))
    (haarRootRadius (finrank ℝ (P j).seed.covector.ker) (rootMass n))
  have hN (n : ℕ) : 0 < rootMass n := by dsimp [rootMass]; positivity
  have hRoot (n : ℕ) : volume (rootDomain n) = ENNReal.ofReal (rootMass n) := by
    simpa only [rootDomain, Fintype.card_fin] using
      volume_haarRootCube_radius _ hqdim (hN n)
  have hfinite (n : ℕ) : ∀ᵐ s ∂(laws n : Measure (Macro × Macro)),
      IsFiniteMeasure (originalIIDMaskedMacroPlan base s : Measure (Pt × Pt)) :=
    ae_originalIIDMaskedMacroPlan_isFiniteMeasure base μ ν hqdim (cost n) (hcost n)
      (selectionScale n) n H hH (coord n) (hcoord n) u hum
  let K : CompactExhaustion Pt := CompactExhaustion.choice Pt
  have hsource (f : C_c(Pt, ℝ)) : Tendsto (fun n ↦ ∫⁻ s : Macro × Macro,
      ENNReal.ofReal |LocalFiniteMeasure.testIntegral
        (originalIIDMaskedMacroInputProjection base s).1 f -
          ∫ e, f e.1 ∂(originalIIDMaskedMacroPlan base s : Measure (Pt × Pt))|
          ∂(laws n : Measure (Macro × Macro))) atTop (𝓝 0) := by
    have heq (n : ℕ) := lintegral_originalIIDMaskedMacroLaw_source_test_error_eq_zero
      base μ ν hqdim (cost n) (hcost n) (selectionScale n) n hH (hcoord n) hum f
    simpa only [laws, originalIIDMaskedMacroPlan, heq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (𝓝 0))
  have htarget (f : C_c(Pt, ℝ)) : Tendsto (fun n ↦ ∫⁻ s : Macro × Macro,
      ENNReal.ofReal |LocalFiniteMeasure.testIntegral
        (originalIIDMaskedMacroInputProjection base s).2 f -
          ∫ e, f e.2 ∂(originalIIDMaskedMacroPlan base s : Measure (Pt × Pt))|
          ∂(laws n : Measure (Macro × Macro))) atTop (𝓝 0) := by
    have hraw := tendsto_originalIID_fixed_seed_literal_target_test_defect_zero
      hcore hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
      hface hgap hdist j cost hcost selectionScale spatialScale hsp hscale
      rootMass hN rootDomain C hC henergy f
    have hfactor (n : ℕ) : rootMass n / (n + 1 : ℕ) = 1 := by
      dsimp [rootMass]
      rw [Nat.cast_add, Nat.cast_one, div_self (by positivity)]
    simp only [hfactor, one_mul] at hraw
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hraw
      (fun _ ↦ zero_le) (fun n ↦ by
        simpa only [laws, originalIIDMaskedMacroPlan, H, coord, rootMass, rootDomain,
          Fintype.card_fin] using lintegral_originalIIDMaskedMacroLaw_target_test_error_le
          base μ ν hqdim (cost n) (hcost n) (selectionScale n) n hH (hcoord n) hum f)
  have htails (f : C_c(Pt, ℝ)) (ε : ℝ≥0∞) (hε : 0 < ε) :=
    exists_originalIID_fixed_seed_uniform_compact_escape
      hcore hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
      hface hgap hdist j (fun _ : Unit ↦ cost) (fun _ ↦ hcost)
      (fun _ : Unit ↦ selectionScale) spatialScale hsp hscale rootMass hN rootDomain hRoot C hC
      (by filter_upwards [henergy] with n hn _; exact hn) f ε hε
  have hsTail (f : C_c(Pt, ℝ)) (ε : ℝ≥0∞) (hε : 0 < ε) :
      ∃ KT : Set Pt, IsCompact KT ∧ ∀ᶠ n in atTop,
        (∫⁻ s, (originalIIDMaskedMacroPlan base s : Measure (Pt × Pt))
          (tsupport f ×ˢ KTᶜ) ∂(laws n : Measure (Macro × Macro))) ≤ ε := by
    obtain ⟨KS, KT, _, hKT, ht⟩ := htails f ε hε
    refine ⟨KT, hKT, ?_⟩
    filter_upwards [ht] with n hn
    exact (lintegral_originalIIDMaskedMacroPlan_measure_le base μ ν hqdim
      (cost n) (hcost n) (selectionScale n) n H hH (coord n) (hcoord n) u hum _).trans
      (by simpa only [H, coord, rootMass, rootDomain, Fintype.card_fin] using (hn ()).1)
  have htTail (f : C_c(Pt, ℝ)) (ε : ℝ≥0∞) (hε : 0 < ε) :
      ∃ KS : Set Pt, IsCompact KS ∧ ∀ᶠ n in atTop,
        (∫⁻ s, (originalIIDMaskedMacroPlan base s : Measure (Pt × Pt))
          (KSᶜ ×ˢ tsupport f) ∂(laws n : Measure (Macro × Macro))) ≤ ε := by
    obtain ⟨KS, KT, hKS, _, ht⟩ := htails f ε hε
    refine ⟨KS, hKS, ?_⟩
    filter_upwards [ht] with n hn
    exact (lintegral_originalIIDMaskedMacroPlan_measure_le base μ ν hqdim
      (cost n) (hcost n) (selectionScale n) n H hH (coord n) (hcoord n) u hum _).trans
      (by simpa only [H, coord, rootMass, rootDomain, Fintype.card_fin] using (hn ()).2)
  have hs := ae_source_input_marginal_eq_of_weak_readout_and_compact_tails Q
    (laws ∘ φ) hweak (originalIIDMaskedMacroPlan base) (continuous_originalIIDMaskedMacroPlan base)
    (fun s ↦ (originalIIDMaskedMacroInputProjection base s).1)
    (continuous_originalIIDMaskedMacroInputProjection base).fst
    (fun n ↦ hfinite (φ n)) K K
    (fun i ↦ (hsource (LocalFiniteMeasure.separatingTest K i)).comp hφ.tendsto_atTop)
    (by intro i ε hε; obtain ⟨KT,hKT,ht⟩ := hsTail (LocalFiniteMeasure.separatingTest K i) ε hε
        exact ⟨KT,hKT,hφ.tendsto_atTop.eventually ht⟩)
  have ht := ae_target_input_marginal_eq_of_weak_readout_and_compact_tails Q
    (laws ∘ φ) hweak (originalIIDMaskedMacroPlan base) (continuous_originalIIDMaskedMacroPlan base)
    (fun s ↦ (originalIIDMaskedMacroInputProjection base s).2)
    (continuous_originalIIDMaskedMacroInputProjection base).snd
    (fun n ↦ hfinite (φ n)) K K
    (fun i ↦ (htarget (LocalFiniteMeasure.separatingTest K i)).comp hφ.tendsto_atTop)
    (by intro i ε hε; obtain ⟨KS,hKS,ht⟩ := htTail (LocalFiniteMeasure.separatingTest K i) ε hε
        exact ⟨KS,hKS,hφ.tendsto_atTop.eventually ht⟩)
  exact hs.and ht

omit hC henergy in
/-- The original supported pressure data supply the actual finite energy budget;
therefore every actual supported-optimizer weak subsequence has its complete
source and target marginals on the same two original masked iid inputs. -/
theorem PopulationLocalPressureCore.ae_originalIID_supported_masked_macro_input_marginals
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (bins : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ)
    (Ksupport : Set M) (hK : IsCompact Ksupport)
    (hμK : ∀ᵐ x ∂μ, x ∈ Ksupport) (hνK : ∀ᵐ y ∂ν, y ∈ Ksupport)
    (f : (Ksupport × Ksupport) →ᵇ ℝ) (g : (M × M) →ᵇ ℝ) (ε probeError : ℝ)
    (hdata : D.originalSupportedWeightUnitDensityPressureData
      (μ := (⟨μ, inferInstance⟩ : ProbabilityMeasure M))
      (ν := (⟨ν, inferInstance⟩ : ProbabilityMeasure M)) γ originalGap bins U
      retentionError splitError Ksupport hK hμK hνK f g ε probeError
      (fun n ↦ canonicalLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure M)
        (⟨ν, inferInstance⟩ : ProbabilityMeasure M) n)
      (fun n ↦ canonicalX n) (fun n ↦ canonicalY n))
    (t : ℝ) (hnorm : ∀ n, spatialScale n ^ 2 = finslerMeanScale E n)
    (hq : 0 < finrank ℝ (P j).seed.covector.ker) :
    let supportedCost := fun n x y ↦ finslerMeanScale E n *
      ((F.lengthEDist x y).toReal - u y + u x) +
        t * finslerCarrierProbe (⟨μ, inferInstance⟩ : ProbabilityMeasure M)
          (⟨ν, inferInstance⟩ : ProbabilityMeasure M)
          Ksupport hK.measurableSet hμK hνK f x y
    ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ Q : ProbabilityMeasure (Macro × Macro),
      Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν (by simpa using hq)
        (supportedCost (φ n))
        (measurable_originalIID_supported_tilt_cost hcomplete
          (⟨μ, inferInstance⟩ : ProbabilityMeasure M) (⟨ν, inferInstance⟩ : ProbabilityMeasure M)
          Ksupport hK.measurableSet hμK hνK u hu f (finslerMeanScale E (φ n)) t)
        1 (φ n)
        (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j)
        (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
        (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale (φ n)))
        (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j
          (spatialScale (φ n)))
        u (by let _supportedMacroMetric : MetricSpace M := F.metricSpace
              exact hu.continuous.measurable)) atTop (𝓝 Q) →
      ∀ᵐ s ∂(Q : Measure (Macro × Macro)),
        (originalIIDMaskedMacroPlan base s : Measure (Pt × Pt)).fst =
          (originalIIDMaskedMacroInputProjection base s).1 ∧
        (originalIIDMaskedMacroPlan base s : Measure (Pt × Pt)).snd =
          (originalIIDMaskedMacroInputProjection base s).2 := by
  let μP : ProbabilityMeasure M := ⟨μ, inferInstance⟩
  let νP : ProbabilityMeasure M := ⟨ν, inferInstance⟩
  let supportedCost := fun n x y ↦ finslerMeanScale E n *
    ((F.lengthEDist x y).toReal - u y + u x) +
      t * finslerCarrierProbe μP νP Ksupport hK.measurableSet hμK hνK f x y
  have hcostSupported (n : ℕ) : Measurable (Function.uncurry (supportedCost n)) :=
    measurable_originalIID_supported_tilt_cost hcomplete μP νP
      Ksupport hK.measurableSet hμK hνK u hu f (finslerMeanScale E n) t
  obtain ⟨Cb,hCb,hbudget⟩ :=
    D.exists_eventually_originalIID_supported_spatial_energy_bound
      (μ := μP) (ν := νP) hcomplete hu γ originalGap bins U retentionError splitError
      Ksupport hK hμK hνK f g ε probeError hdata t spatialScale hnorm
  dsimp only
  intro φ hφ Q hweak
  exact ae_originalIID_fixed_seed_masked_macro_input_marginals
    (hcore := hcore) (hrecovery := hrecovery) (hF := hF) (hcomplete := hcomplete)
    (hu := hu) (ha := ha) (hinj := hinj) (hκ := hκ) (horder := horder)
    (hbalance := hbalance) (hA := hA) (hB := hB) (hμ := hμ) (hν := hν)
    (hreg := hreg) (hμreg := hμreg) (hface := hface) (hgap := hgap) (hdist := hdist)
    (cost := supportedCost) (hcost := hcostSupported) (selectionScale := fun _ ↦ 1)
    (spatialScale := spatialScale) (hsp := hsp) (hscale := hscale)
    (j := j) (C := Cb) (hC := hCb) (henergy := hbudget) (base := base) hq φ hφ Q hweak

end FinslerClosure

end OTSelector.Reconstruction


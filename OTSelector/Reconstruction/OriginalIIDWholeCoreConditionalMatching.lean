import OTSelector.Reconstruction.OriginalIIDMacroFrameCover
import OTSelector.Reconstruction.OriginalIIDActualConditionalMatching
import OTSelector.Reconstruction.OriginalIIDMaskedMacroForwardClock

/-!
# Full conditional original matching over the whole core

All rational frames retain the same original iid optimizer subsequence. Root translation
moves only the original spatial center. It preserves normalized finite root mass and the
unnormalized owner restrictions; clocks, original samples and edge normalization remain
those of the original experiment.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction BigOperators ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 20000

/-- A constant coordinate translation is precisely the opposite original root translation. -/
theorem physicalSceneRootedPlan_coord_sub_const
    {M ι : Type*} [MeasurableSpace M] [Fintype ι]
    (π : Measure (M × M)) (coord : M → (ι → ℝ)) (u : M → ℝ) (N : ℝ) (d z : ι → ℝ) :
    physicalSceneRootedPlan π (fun x ↦ coord x - d) u N z =
      physicalSceneRootedPlan π coord u N (d + z) := by
  unfold physicalSceneRootedPlan
  congr 2
  funext p
  simp only [physicalSceneRootedObservation]
  congr 2 <;> abel

/-- Translation preserves the original normalized root measure with the same mass factor. -/
theorem map_cavityRootMeasure_add_const
    {ι : Type*} [Fintype ι] (D : Set (ι → ℝ)) (N : ℝ) (d : ι → ℝ) :
    (cavityRootMeasure volume D N).map (fun z ↦ d + z) =
      cavityRootMeasure volume ((fun z ↦ d + z) '' D) N :=
  (((measurePreserving_add_left (volume : Measure (ι → ℝ)) d).restrict_image_emb
    (measurableEmbedding_addLeft d) D).smul_measure (ENNReal.ofReal N)⁻¹).map_eq

/-- Every root observable, including nonmeasurable auxiliary estimates, transports through
one original root translation. The normalization is unchanged. -/
theorem lintegral_cavityRootMeasure_add_const
    {ι : Type*} [Fintype ι] (D : Set (ι → ℝ)) (N : ℝ) (d : ι → ℝ)
    (f : (ι → ℝ) → ℝ≥0∞) :
    (∫⁻ z, f (d + z) ∂cavityRootMeasure volume D N) =
      ∫⁻ z, f z ∂cavityRootMeasure volume ((fun z ↦ d + z) '' D) N := by
  rw [← map_cavityRootMeasure_add_const]
  exact ((measurableEmbedding_addLeft d).lintegral_map f).symm


open Metric Module Manifold OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped ContDiff
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
local instance iidWholeCoreTranslatedMarginalInst6 : StandardBorelSpace ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) := inferInstance
local instance iidWholeCoreTranslatedMarginalInst7 : TopologicalSpace (LocalConfiguration base) := LocalConfiguration.vagueTopology base
local instance iidWholeCoreTranslatedMarginalInst8 : BorelSpace (LocalConfiguration base) := LocalConfiguration.vagueBorelSpace
local instance iidWholeCoreTranslatedMarginalInst9 : PolishSpace (LocalConfiguration base) := LocalConfiguration.vaguePolishSpace
local instance iidWholeCoreTranslatedMarginalInst10 : PolishSpace (LocalFiniteMeasure
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
theorem ae_originalIID_fixed_seed_translated_masked_macro_input_marginals
    (offset : ℕ → Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)
    (hq : 0 < finrank ℝ (P j).seed.covector.ker)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (Q : ProbabilityMeasure (Macro × Macro))
    (hweak : Tendsto (fun n ↦
      originalIIDMaskedBipartiteMacroLaw base μ ν (by simpa using hq)
        (cost (φ n)) (hcost (φ n)) (selectionScale (φ n)) (φ n)
        (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j)
        (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
        (fun x ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale (φ n)) x - offset (φ n))
        ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j
          (spatialScale (φ n))).sub measurable_const)
        u (by let _inst : MetricSpace M := F.metricSpace; exact hu.continuous.measurable))
        atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (Macro × Macro)),
      (originalIIDMaskedMacroPlan base s : Measure (Pt × Pt)).fst =
        (originalIIDMaskedMacroInputProjection base s).1 ∧
      (originalIIDMaskedMacroPlan base s : Measure (Pt × Pt)).snd =
        (originalIIDMaskedMacroInputProjection base s).2 := by
  let _inst : MetricSpace M := F.metricSpace
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
  let coord := fun n x ↦ physicalSceneOriginalSeedScaledPosition
    (P := P) (a := a) j (spatialScale n) x - offset n
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  have hcoord (n : ℕ) : Measurable (coord n) :=
    (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (spatialScale n)).sub
      (measurable_const : Measurable (fun _ : M ↦ offset n))
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
  let shiftedRootDomain := fun n ↦ (fun z ↦ offset n + z) '' rootDomain n
  have hShiftRoot (n : ℕ) : volume (shiftedRootDomain n) = ENNReal.ofReal (rootMass n) := by
    have h := (measurableEmbedding_addLeft (offset n)).map_apply
      (volume : Measure (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)) (shiftedRootDomain n)
    rw [(measurePreserving_add_left volume (offset n)).map_eq] at h
    rw [h]
    change volume ((fun x ↦ offset n + x) ⁻¹' ((fun x ↦ offset n + x) '' rootDomain n)) = _
    rw [Set.preimage_image_eq _ (fun _ _ h ↦ add_left_cancel h), hRoot n]
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
      rootMass hN shiftedRootDomain C hC henergy f
    dsimp only at hraw
    simp only [shiftedRootDomain] at hraw
    simp_rw [← lintegral_cavityRootMeasure_add_const] at hraw
    have hfactor (n : ℕ) : rootMass n / (n + 1 : ℕ) = 1 := by
      dsimp [rootMass]
      rw [Nat.cast_add, Nat.cast_one, div_self (by positivity)]
    simp only [hfactor, one_mul] at hraw
    have hrawShift := hraw
    simp only [← physicalSceneRootedPlan_coord_sub_const, ← sub_sub] at hrawShift
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrawShift
      (fun _ ↦ zero_le) (fun n ↦ by
        simpa only [laws, originalIIDMaskedMacroPlan, H, coord, rootMass, rootDomain,
          Fintype.card_fin] using lintegral_originalIIDMaskedMacroLaw_target_test_error_le
          base μ ν hqdim (cost n) (hcost n) (selectionScale n) n hH (hcoord n) hum f)
  have htails (f : C_c(Pt, ℝ)) (ε : ℝ≥0∞) (hε : 0 < ε) :=
    exists_originalIID_fixed_seed_uniform_compact_escape
      hcore hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
      hface hgap hdist j (fun _ : Unit ↦ cost) (fun _ ↦ hcost)
      (fun _ : Unit ↦ selectionScale) spatialScale hsp hscale rootMass hN shiftedRootDomain hShiftRoot C hC
      (by filter_upwards [henergy] with n hn _; exact hn) f ε hε
  have hsTail (f : C_c(Pt, ℝ)) (ε : ℝ≥0∞) (hε : 0 < ε) :
      ∃ KT : Set Pt, IsCompact KT ∧ ∀ᶠ n in atTop,
        (∫⁻ s, (originalIIDMaskedMacroPlan base s : Measure (Pt × Pt))
          (tsupport f ×ˢ KTᶜ) ∂(laws n : Measure (Macro × Macro))) ≤ ε := by
    obtain ⟨KS, KT, _, hKT, ht⟩ := htails f ε hε
    dsimp only at ht
    simp only [shiftedRootDomain] at ht
    simp_rw [← lintegral_cavityRootMeasure_add_const] at ht
    simp only [← physicalSceneRootedPlan_coord_sub_const] at ht
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
    dsimp only at ht
    simp only [shiftedRootDomain] at ht
    simp_rw [← lintegral_cavityRootMeasure_add_const] at ht
    simp only [← physicalSceneRootedPlan_coord_sub_const] at ht
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

end FinslerClosure

section WholeCoreScene
variable {q : ℕ} {M : Type*} [MeasurableSpace M]
local instance iidWholeCoreConditionalMatchingPointStandardBorel : StandardBorelSpace (((Fin q) → ℝ) × ℝ) := inferInstance
local instance iidWholeCoreConditionalMatchingPlanPolish : PolishSpace
    (LocalFiniteMeasure ((((Fin q) → ℝ) × ℝ) × (((Fin q) → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local instance iidWholeCoreConditionalMatchingInputPolish : PolishSpace
    (LocalFiniteMeasure (((Fin q) → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance iidWholeCoreConditionalMatchingInputNonempty : Nonempty
    (LocalFiniteMeasure (((Fin q) → ℝ) × ℝ)) := ⟨⟨0,inferInstance⟩⟩
local instance iidWholeCoreConditionalMatchingPlanNonempty : Nonempty
    (LocalFiniteMeasure ((((Fin q) → ℝ) × ℝ) × (((Fin q) → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩
local notation "base" => (0 : ((Fin q) → ℝ) × ℝ)
local instance iidWholeCoreConditionalMatchingConfigurationTopology : TopologicalSpace (LocalConfiguration base) :=
  LocalConfiguration.vagueTopology base
local instance iidWholeCoreConditionalMatchingConfigurationBorel : BorelSpace (LocalConfiguration base) :=
  LocalConfiguration.vagueBorelSpace
local instance iidWholeCoreConditionalMatchingConfigurationPolish : PolishSpace (LocalConfiguration base) :=
  LocalConfiguration.vaguePolishSpace
set_option quotPrecheck false
local notation "Pt" => ((Fin q) → ℝ) × ℝ
local notation "Scene" => OriginalIIDMaskedMacroInputScene (Fin q)
local notation "Macro" => OriginalIIDMaskedMacroCarrier base
local instance iidWholeCoreConditionalMatchingMacroPairPolish : PolishSpace (Macro × Macro) := inferInstance
local instance iidWholeCoreConditionalMatchingSceneBorel : BorelSpace Scene := inferInstance
local instance iidWholeCoreConditionalMatchingMacroBorel : BorelSpace Macro := inferInstance
local instance iidWholeCoreConditionalMatchingMacroPairBorel : BorelSpace (Macro × Macro) := inferInstance


/-- The complete raw conditional scene conclusion, retaining original input mass, both
plans, all spatial rerootings and the original positive forward clock gap. -/
def OriginalIIDConditionalMatchingProfile (gap θ : ℝ) (α β : Measure ℝ)
    (input : Measure (LocalFiniteMeasure Pt × LocalFiniteMeasure Pt)) (Q : Measure Scene) : Prop :=
  IsProbabilityMeasure Q ∧ Q.map Prod.snd = input ∧
    (∀ w : Fin q → ℝ, MeasurePreserving (originalIIDMaskedMacroInputSceneReroot w) Q Q) ∧
    (∀ H G : LegalNonnegativeInputTest Pt,
      (∫ z, legalInputMeasureLaplacePair H G z ∂Q.map Prod.snd) =
        Real.exp (-(θ * ((∫ x, 1 - Real.exp (-H.1 x) ∂volume.prod α) +
          ∫ y, 1 - Real.exp (-G.1 y) ∂volume.prod β)))) ∧
    IndepFun Prod.fst Prod.snd (Q.map Prod.snd) ∧
    ∀ᵐ z ∂Q,
      z.1.1 = z.1.2 ∧
      IsFullOriginalBipartiteMatching base base z.1.1 z.2.1 z.2.2 ∧
      IsFullOriginalBipartiteMatching base base z.1.2 z.2.1 z.2.2 ∧
      (∀ᵐ e ∂(z.1.1 : Measure (Pt × Pt)), gap / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(z.1.2 : Measure (Pt × Pt)), gap / 2 ≤ e.2.2 - e.1.2)

/-- The positive forward-clock event is measurable on the actual full scene carrier. -/
theorem measurableSet_originalIIDConditional_clock_gap (gap : ℝ) :
    MeasurableSet {z : Scene |
      (∀ᵐ e ∂(z.1.1 : Measure (Pt × Pt)), gap / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(z.1.2 : Measure (Pt × Pt)), gap / 2 ≤ e.2.2 - e.1.2)} := by
  have hb : MeasurableSet {e : Pt × Pt | ¬ gap / 2 ≤ e.2.2 - e.1.2} :=
    (measurableSet_le measurable_const (measurable_snd.snd.sub measurable_fst.snd)).compl
  have hm : MeasurableSet {π : LocalFiniteMeasure (Pt × Pt) |
      ∀ᵐ e ∂(π : Measure (Pt × Pt)), gap / 2 ≤ e.2.2 - e.1.2} := by
    change MeasurableSet {π : LocalFiniteMeasure (Pt × Pt) |
      (π : Measure (Pt × Pt)) {e | ¬ gap / 2 ≤ e.2.2 - e.1.2} = 0}
    exact measurableSet_eq_fun ((Measure.measurable_coe hb).comp measurable_localFiniteMeasure_coe)
      measurable_const
  exact (hm.preimage measurable_fst.fst).inter (hm.preimage measurable_fst.snd)

/-- The full scene conditional kernels of the prescribed actual weak law inherit their
original forward gaps. No new weak subsequence or scene law is chosen. -/
theorem ae_conditional_originalIIDMaskedMacro_clock_gap
    (L : ProbabilityMeasure (Macro × Macro)) (gap : ℝ)
    (hg : ∀ᵐ z ∂(L : Measure (Macro × Macro)),
      (∀ᵐ e ∂(z.1.2.1.1 : Measure (Pt × Pt)), gap / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(z.1.2.1.2 : Measure (Pt × Pt)), gap / 2 ≤ e.2.2 - e.1.2)) :
    let ρ := (L.map
      (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable :
      Measure ((Fin q → ℝ) × Scene))
    ∀ᵐ y ∂ρ.fst, ∀ᵐ z ∂ρ.condKernel y,
      (∀ᵐ e ∂(z.1.1 : Measure (Pt × Pt)), gap / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(z.1.2 : Measure (Pt × Pt)), gap / 2 ≤ e.2.2 - e.1.2) := by
  dsimp only
  apply ae_ae_condKernel_of_ae_joint
  apply (ae_map_iff
    (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable
    ((measurableSet_originalIIDConditional_clock_gap gap).preimage measurable_snd)).mpr
  exact hg

/-- Actual integer/full-marginal data and the already identified original input profile
assemble full stationary conditional matchings on the same prescribed macro weak law.
The final D consumer below derives the two raw marginal/clock hypotheses from its actual
original optimizer energy, rather than asking for a finished matching or stationary law. -/
theorem ae_originalIIDMaskedMacro_conditional_matching_of_actual_data
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < q)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → (Fin q → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (m : ℕ → ℕ) (hm : StrictMono m)
    (L : ProbabilityMeasure (Macro × Macro))
    (hweak : Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν (by simpa using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu) atTop (𝓝 L))
    (hfull : ∀ᵐ z ∂(L : Measure (Macro × Macro)),
      (originalIIDMaskedMacroPlan base z : Measure (Pt × Pt)).fst =
        (originalIIDMaskedMacroInputProjection base z).1 ∧
      (originalIIDMaskedMacroPlan base z : Measure (Pt × Pt)).snd =
        (originalIIDMaskedMacroInputProjection base z).2)
    (gap : ℝ) (hg : ∀ᵐ z ∂(L : Measure (Macro × Macro)),
      (∀ᵐ e ∂(z.1.2.1.1 : Measure (Pt × Pt)), gap / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(z.1.2.1.2 : Measure (Pt × Pt)), gap / 2 ≤ e.2.2 - e.1.2))
    (η : ProbabilityMeasure (Fin q → ℝ)) (A : Set (Fin q → ℝ))
    (c0 : Fin q → ℝ) (Γ : Kernel (Fin q → ℝ) (LocalFiniteMeasure Pt × LocalFiniteMeasure Pt))
    (θ : (Fin q → ℝ) → ℝ) (hθ : ∀ c, 0 ≤ θ c)
    (α β : (Fin q → ℝ) → Measure ℝ)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (hroot : ((L.map (measurable_originalIIDMaskedMacroTaggedInputProjection base).aemeasurable :
      Measure ((Fin q → ℝ) × (LocalFiniteMeasure Pt × LocalFiniteMeasure Pt)))).fst = (η : Measure (Fin q → ℝ)))
    (hinput : ∀ᵐ y ∂(η : Measure (Fin q → ℝ)).restrict A,
      let σ := (L.map (measurable_originalIIDMaskedMacroTaggedInputProjection base).aemeasurable :
        Measure ((Fin q → ℝ) × (LocalFiniteMeasure Pt × LocalFiniteMeasure Pt)))
      σ.condKernel y = Γ (c0 + y) ∧
      (∀ H G : LegalNonnegativeInputTest Pt,
        (∫ z, legalInputMeasureLaplacePair H G z ∂σ.condKernel y) =
          Real.exp (-(θ (c0 + y) * ((∫ x, 1 - Real.exp (-H.1 x) ∂volume.prod (α (c0 + y))) +
            ∫ z, 1 - Real.exp (-G.1 z) ∂volume.prod (β (c0 + y)))))) ∧
      IndepFun Prod.fst Prod.snd (σ.condKernel y)) :
    let ρ := (L.map
      (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable :
      Measure ((Fin q → ℝ) × Scene))
    ρ.fst = (η : Measure (Fin q → ℝ)) ∧
      ∀ᵐ y ∂(η : Measure (Fin q → ℝ)).restrict A,
        OriginalIIDConditionalMatchingProfile gap (θ (c0 + y)) (α (c0 + y)) (β (c0 + y))
          (Γ (c0 + y)) (ρ.condKernel y) := by
  let ρ : Measure ((Fin q → ℝ) × Scene) := (L.map
    (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable :
    Measure ((Fin q → ℝ) × Scene))
  let σ : Measure ((Fin q → ℝ) × (LocalFiniteMeasure Pt × LocalFiniteMeasure Pt)) := (L.map
    (measurable_originalIIDMaskedMacroTaggedInputProjection base).aemeasurable :
    Measure ((Fin q → ℝ) × (LocalFiniteMeasure Pt × LocalFiniteMeasure Pt)))
  have hσ : σ = ρ.map (Prod.map id (Prod.snd : Scene → LocalFiniteMeasure Pt × LocalFiniteMeasure Pt)) :=
    originalMaskedMacro_taggedInput_eq_fullScene_input_projection base L
  have hproj := ae_condKernel_map_readout_eq_of_joint_projection ρ
    (Prod.snd : Scene → LocalFiniteMeasure Pt × LocalFiniteMeasure Pt) measurable_snd
  dsimp only at hproj
  simp only [← hσ] at hproj
  have hρfst : ρ.fst = (η : Measure (Fin q → ℝ)) := hproj.1.symm.trans hroot
  have hCountL := ae_isLegalCountingMeasure_of_originalIIDMaskedBipartiteMacroLaw_tendsto
    base μ ν (by simpa using hq) cost hcost k (fun _ ↦ H) (fun _ ↦ hH)
    coord hcoord u hu m L hweak
  have hData := ae_conditional_originalMaskedMacro_integer_full_marginals base L hCountL hfull
  have hCounts := ae_conditional_originalMaskedMacro_input_counting base L
  have hStationary := joint_and_ae_conditional_originalIIDMaskedMacroInputSceneReroot_of_tendsto
    base μ ν (by simpa using hq) cost hcost k H hH coord hcoord u hu m hm.tendsto_atTop hweak
  have hShared := ae_conditional_originalIIDMaskedMacroInputScene_plan_pair_eq_of_tendsto
    base μ ν (by simpa using hq) cost hcost k H hH coord hcoord u hu m hweak
  have hGap := ae_conditional_originalIIDMaskedMacro_clock_gap L gap hg
  have hRestrict (p : (Fin q → ℝ) → Prop) (hp : ∀ᵐ c ∂ρ.fst, p c) :
      ∀ᵐ c ∂(η : Measure (Fin q → ℝ)).restrict A, p c := by
    apply ae_restrict_of_ae
    simpa only [← hρfst] using hp
  refine ⟨hρfst, ?_⟩
  filter_upwards [hinput, hRestrict _ hData, hRestrict _ hCounts, hRestrict _ hStationary.2,
    hRestrict _ hShared, hRestrict _ hGap, hRestrict _ hproj.2] with y hi hd hc hs he hg hp
  have hProfile : ∀ H G : LegalNonnegativeInputTest Pt,
      (∫ z, legalInputMeasureLaplacePair H G z ∂(ρ.condKernel y).map Prod.snd) =
        Real.exp (-(θ (c0 + y) * ((∫ x, 1 - Real.exp (-H.1 x) ∂volume.prod (α (c0 + y))) +
          ∫ z, 1 - Real.exp (-G.1 z) ∂volume.prod (β (c0 + y))))) := by
    rw [hp]
    exact hi.2.1
  have hCountMeas : MeasurableSet {z : LocalFiniteMeasure Pt × LocalFiniteMeasure Pt |
      IsLegalCountingMeasure base z.1 ∧ IsLegalCountingMeasure base z.2} :=
    ((isClosed_isLegalCountingMeasure base).measurableSet.preimage measurable_fst).inter
      ((isClosed_isLegalCountingMeasure base).measurableSet.preimage measurable_snd)
  have hRead : Measurable (Prod.snd : Scene → LocalFiniteMeasure Pt × LocalFiniteMeasure Pt) := measurable_snd
  have hInputCount : ∀ᵐ z ∂(ρ.condKernel y).map Prod.snd,
      IsLegalCountingMeasure base z.1 ∧ IsLegalCountingMeasure base z.2 :=
    (ae_map_iff hRead.aemeasurable hCountMeas).mpr hc
  let _iidWholeCoreReadProbability : IsProbabilityMeasure ((ρ.condKernel y).map Prod.snd) :=
    Measure.isProbabilityMeasure_map hRead.aemeasurable
  have hSimple := ae_simple_pair_of_compact_poisson_profile q hq (θ (c0 + y)) (hθ _)
    (α (c0 + y)) (β (c0 + y)) ((ρ.condKernel y).map Prod.snd) hProfile hInputCount
  have hSimpleMeas : MeasurableSet {z : LocalFiniteMeasure Pt × LocalFiniteMeasure Pt |
      IsLegalSimpleCountingMeasure base z.1 ∧ IsLegalSimpleCountingMeasure base z.2} :=
    ((measurableSet_isLegalSimpleCountingMeasure base).preimage measurable_fst).inter
      ((measurableSet_isLegalSimpleCountingMeasure base).preimage measurable_snd)
  have hFullMatch : ∀ᵐ z ∂ρ.condKernel y,
      IsFullOriginalBipartiteMatching base base z.1.1 z.2.1 z.2.2 := by
    filter_upwards [hd, (ae_map_iff hRead.aemeasurable hSimpleMeas).mp hSimple] with z hz hzSimple
    exact isFullOriginalBipartiteMatching_of_counting_simple_marginals
      base base z.1.1 z.2.1 z.2.2 hz.1 hzSimple.1 hzSimple.2 hz.2.1 hz.2.2
  refine ⟨inferInstance, hp.trans hi.1, hs, hProfile, ?_, ?_⟩
  · rw [hp]
    exact hi.2.2
  · filter_upwards [he, hFullMatch, hg] with z he hm hgg
    exact ⟨he, hm, he ▸ hm, hgg⟩

end WholeCoreScene

section WholeCoreSupportedActual
open Metric Module Manifold OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped ContDiff NNReal
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

local instance iidWholeCoreSupportedMatchingCorePointStandardBorel (q : ℕ) : StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance iidWholeCoreSupportedMatchingCoreConfigTopology (q : ℕ) :
    TopologicalSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueTopology _
local instance iidWholeCoreSupportedMatchingCoreConfigBorel (q : ℕ) :
    BorelSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueBorelSpace
local instance iidWholeCoreSupportedMatchingCoreConfigPolish (q : ℕ) :
    PolishSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vaguePolishSpace
local instance iidWholeCoreSupportedMatchingCoreInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance iidWholeCoreSupportedMatchingCorePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidWholeCoreSupportedMatchingCoreInputNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := ⟨⟨0,inferInstance⟩⟩
local instance iidWholeCoreSupportedMatchingCorePlanNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩

local instance iidWholeCoreSupportedMatchingCoreMacroPairPolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance iidWholeCoreSupportedMatchingCoreSceneBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidWholeCoreSupportedMatchingCoreMacroBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance iidWholeCoreSupportedMatchingCoreMacroPairBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance

local instance iidWholeCoreSupportedMatchingCoreScenePolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidWholeCoreSupportedMatchingCoreSceneStandardBorel (q : ℕ) :
    StandardBorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidWholeCoreSupportedMatchingCoreTaggedSceneBorel (q : ℕ) :
    BorelSpace ((Fin q → ℝ) × OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance

include hcore hrecovery hκ horder hbalance hA hB hμ hν hreg hμreg hface hgap hdist


/-- One common subsequence of the same actual supported optimizer in all rational frames
gives full stationary two-input matchings, original intensity and positive forward clocks
for almost every original center in the entire core. Every owner retains its original mass. -/
theorem PopulationLocalPressureCore.original_supported_whole_core_conditional_full_matching
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
    (t : ℝ) (hdim : 2 ≤ finrank ℝ E) (i : Fin D.haar.continuous.count) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let V := Fin q → ℝ
    let X := V × ℝ
    let T := LocalFiniteMeasure X × LocalFiniteMeasure X
    let Scene := OriginalIIDMaskedMacroInputScene (Fin q)
    let Macro := OriginalIIDMaskedMacroCarrier (0 : X)
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let φ := fun x ↦ e (R (a x))
    let K := e '' (R '' C.roots)
    let scale := physicalSceneCanonicalHaarScale q
    let mask := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := μ.map a) C.seedIndex
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let θ := fun c ↦ originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex (ref c)
    let α := fun c ↦ condDistrib u a μ (ref c)
    let β := fun c ↦ condDistrib u a ν (ref c)
    let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
      (physicalScene_centered_unitCube_mass (Fin q))
    let cost := fun n x y ↦ finslerMeanScale E n *
      ((F.lengthEDist x y).toReal - u y + u x) +
        t * finslerCarrierProbe (⟨μ,inferInstance⟩ : ProbabilityMeasure M)
          (⟨ν,inferInstance⟩ : ProbabilityMeasure M) Ksupport hK.measurableSet hμK hνK f x y
    let hcost : ∀ n, Measurable (Function.uncurry (cost n)) := fun n ↦
      measurable_originalIID_supported_tilt_cost hcomplete
      (⟨μ,inferInstance⟩ : ProbabilityMeasure M) (⟨ν,inferInstance⟩ : ProbabilityMeasure M)
      Ksupport hK.measurableSet hμK hνK u hu f (finslerMeanScale E n) t
    let hm : MeasurableSet mask := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj C.seedIndex
    let hφ : Measurable φ := by
      have hp := measurable_physicalSceneOriginalSeedScaledPosition
        (P := P) (a := a) hF hcomplete hu ha hinj C.seedIndex (1 : ℝ)
      change Measurable (fun x ↦ (1 : ℝ) • φ x) at hp
      simpa only [one_smul] using hp
    let huM : Measurable u := by
      let _iidWholeCoreMatchingMetric : MetricSpace M := F.metricSpace
      exact hu.continuous.measurable
    ∃ Γ : Kernel V T, IsMarkovKernel Γ ∧
      ∃ m : ℕ → ℕ, StrictMono m ∧ ∃ Q : ℕ → ProbabilityMeasure (Macro × Macro),
        (∀ j, Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw (0 : X) μ ν
          (by simpa using original_seed_transverse_finrank_pos S hdim)
          (cost (m n)) (hcost (m n)) 1 (m n) mask hm
          (fun x ↦ scale (m n) • (φ x - originalMacroFrameCenter q j))
          ((hφ.sub measurable_const).const_smul (scale (m n))) u huM) atTop (𝓝 (Q j))) ∧
        (∀ j,
          let ρ := ((Q j).map
            (continuous_originalIIDMaskedMacroInputSceneProjection (0 : X)).measurable.aemeasurable :
            Measure (V × Scene))
          ρ.fst = (η : Measure V) ∧
          ∀ᵐ y ∂(η : Measure V).restrict
              ((fun y ↦ originalMacroFrameCenter q j + y) ⁻¹' originalMacroFrameOwner q K j),
            OriginalIIDConditionalMatchingProfile gap (θ (originalMacroFrameCenter q j + y))
              (α (originalMacroFrameCenter q j + y)) (β (originalMacroFrameCenter q j + y))
              (Γ (originalMacroFrameCenter q j + y)) (ρ.condKernel y)) ∧
        ∀ᵐ c ∂(volume : Measure V).restrict K, ∃ j,
          c ∈ originalMacroFrameOwner q K j ∧
          let ρ := ((Q j).map
            (continuous_originalIIDMaskedMacroInputSceneProjection (0 : X)).measurable.aemeasurable :
            Measure (V × Scene))
          OriginalIIDConditionalMatchingProfile gap (θ c) (α c) (β c)
            (Γ c) (ρ.condKernel (c - originalMacroFrameCenter q j)) := by
  intro C S q V X T Scene Macro R e φ K scale mask ref θ α β η cost hcost hmask hφ huM
  let _iidWholeCoreMatchingMetric : MetricSpace M := F.metricSpace
  let _iidWholeCoreMatchingProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _iidWholeCoreMatchingPolish : PolishSpace M := inferInstance
  let _iidWholeCoreMatchingRootBorel : BorelSpace (ℚ → M) := inferInstance
  have hq : 0 < q := original_seed_transverse_finrank_pos S hdim
  have hqdim : 0 < Fintype.card (Fin q) := by simpa using hq
  have hdimker : q = finrank ℝ E - 1 := by
    have hh : q + 1 = finrank ℝ E := by
      simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using
        S.normalization.toLinearEquiv.finrank_eq
    omega
  have hnormMean (n : ℕ) : scale n ^ 2 = finslerMeanScale E n := by
    rw [show scale n = ((n : ℝ) + 1) ^ (1 / (q : ℝ)) from
      physicalSceneCanonicalHaarScale_eq_rpow q n]
    unfold finslerMeanScale
    rw [Nat.cast_add, Nat.cast_one, ← Real.rpow_natCast (((n : ℝ) + 1) ^ (1 / (q : ℝ))) 2,
      ← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ) + 1), hdimker]
    congr 1
    ring
  have hscale2 : Tendsto (fun n ↦ scale n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).comp
      (tendsto_physicalSceneCanonicalHaarScale q hq)
  have hRset : MeasurableSet (R '' C.roots) :=
    D.haar.measurable_cell_label_image hcomplete i C.roots_compact.measurableSet Subset.rfl
  have hKcore : MeasurableSet K :=
    e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hRset
  obtain ⟨Γ, hΓ, hOwners⟩ := D.original_macro_frame_owner_limits
    hF hcomplete hu ha hinj hdim i cost hcost (fun _ ↦ 1)
  obtain ⟨m, hm, Q, hQ, _hGlobalInput⟩ := hOwners
  obtain ⟨Cenergy, hCenergy, hbudget⟩ := D.exists_eventually_originalIID_supported_spatial_energy_bound
    (μ := (⟨μ, inferInstance⟩ : ProbabilityMeasure M))
    (ν := (⟨ν, inferInstance⟩ : ProbabilityMeasure M)) hcomplete hu γ originalGap bins U retentionError splitError Ksupport hK hμK hνK
    f g ε probeError hdata t scale hnormMean
  have hFrames (j : ℕ) :
      let ρ := ((Q j).map
        (continuous_originalIIDMaskedMacroInputSceneProjection (0 : X)).measurable.aemeasurable :
        Measure (V × Scene))
      ρ.fst = (η : Measure V) ∧
      ∀ᵐ y ∂(η : Measure V).restrict
          ((fun y ↦ originalMacroFrameCenter q j + y) ⁻¹' originalMacroFrameOwner q K j),
        OriginalIIDConditionalMatchingProfile gap (θ (originalMacroFrameCenter q j + y))
          (α (originalMacroFrameCenter q j + y)) (β (originalMacroFrameCenter q j + y))
          (Γ (originalMacroFrameCenter q j + y)) (ρ.condKernel y) := by
    let coord := fun n x ↦ scale n • φ x - scale n • originalMacroFrameCenter q j
    have hcoord (n : ℕ) : Measurable (coord n) :=
      (hφ.const_smul (scale n)).sub measurable_const
    have hw : Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw (0 : X) μ ν hqdim
        (cost (m n)) (hcost (m n)) 1 (m n) mask hmask
        (coord (m n)) (hcoord (m n)) u huM) atTop (𝓝 (Q j)) := by
      simpa only [coord, smul_sub] using (hQ j).1
    have hFull := ae_originalIID_fixed_seed_translated_masked_macro_input_marginals
      (hcore := hcore) (hrecovery := hrecovery) (hF := hF) (hcomplete := hcomplete)
      (hu := hu) (ha := ha) (hinj := hinj) (hκ := hκ) (horder := horder)
      (hbalance := hbalance) (hA := hA) (hB := hB) (hμ := hμ) (hν := hν)
      (hreg := hreg) (hμreg := hμreg) (hface := hface) (hgap := hgap) (hdist := hdist)
      (cost := cost) (hcost := hcost) (selectionScale := fun _ ↦ 1)
      (spatialScale := scale) (hsp := physicalSceneCanonicalHaarScale_pos q) (hscale := hscale2)
      (j := C.seedIndex) (C := Cenergy) (hC := hCenergy) (henergy := hbudget) (base := (0 : X))
      (fun n ↦ scale n • originalMacroFrameCenter q j) hq m hm (Q j) (by convert hw using 1; rfl)
    have hClock := ae_originalIIDMaskedMacro_weak_limit_clock_gap (0 : X) μ ν hqdim
      hgap hdist hμ hν cost hcost (fun _ ↦ 1) (fun _ ↦ mask) (fun _ ↦ hmask)
      coord hcoord hu (fun n ↦ scale n ^ 2) (fun n ↦ sq_pos_of_pos (physicalSceneCanonicalHaarScale_pos q n))
      hscale2 Cenergy hCenergy hbudget m hm (Q j) hw
    exact ae_originalIIDMaskedMacro_conditional_matching_of_actual_data μ ν hq cost hcost
      (fun _ ↦ 1) mask hmask coord hcoord u huM m hm (Q j) hw hFull gap hClock η
      ((fun y ↦ originalMacroFrameCenter q j + y) ⁻¹' originalMacroFrameOwner q K j)
      (originalMacroFrameCenter q j) Γ θ
      (fun c ↦ mul_nonneg (NNReal.coe_nonneg _)
        (populationAtlasTheta_nonneg P a κ (μ.map a) C.seedIndex (ref c)))
      α β (hQ j).2.1 (hQ j).2.2.2
  refine ⟨Γ, hΓ, m, hm, Q, (fun j ↦ (hQ j).1), hFrames, ?_⟩
  apply ae_originalMacroFrameOwner_glue q K volume
  intro j
  let ρ : Measure (V × Scene) := ((Q j).map
    (continuous_originalIIDMaskedMacroInputSceneProjection (0 : X)).measurable.aemeasurable :
    Measure (V × Scene))
  have hc : ∀ᵐ c ∂(volume : Measure V).restrict (originalMacroFrameOwner q K j),
      OriginalIIDConditionalMatchingProfile gap (θ c) (α c) (β c)
        (Γ c) (ρ.condKernel (c - originalMacroFrameCenter q j)) := by
    apply (ae_originalMacroFrameOwner_iff q hKcore j _).mpr
    filter_upwards [(hFrames j).2] with y hy
    change OriginalIIDConditionalMatchingProfile gap (θ (originalMacroFrameCenter q j + y))
      (α (originalMacroFrameCenter q j + y)) (β (originalMacroFrameCenter q j + y))
      (Γ (originalMacroFrameCenter q j + y)) (ρ.condKernel y) at hy
    simpa only [add_sub_cancel_left] using hy
  filter_upwards [hc, ae_restrict_mem (measurableSet_originalMacroFrameOwner q hKcore j)] with c hcc hcj
  exact ⟨j, hcj, hcc⟩

end WholeCoreSupportedActual
end OTSelector.Reconstruction

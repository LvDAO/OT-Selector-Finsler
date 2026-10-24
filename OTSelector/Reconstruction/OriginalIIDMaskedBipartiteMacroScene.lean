import OTSelector.PointProcess.LocalConfigurationTightness
import OTSelector.Reconstruction.OriginalIIDBipartiteMacroScene
import OTSelector.PointProcess.LocalConfigurationMaskedTuple
import OTSelector.Probability.CommonIteratedWeakSubsequence

/-! The same original iid optimizer and Haar root jointly retain both original
input clouds with the literal fixed physical seed mask. No discarded input is
replaced by an artificial point. -/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
variable {M ι : Type*} [MeasurableSpace M] [Fintype ι]
variable (base : (ι → ℝ) × ℝ)
local instance maskedIidMacroStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance maskedIidMacroConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance maskedIidMacroConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance maskedIidMacroConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance maskedIidMacroPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
set_option quotPrecheck false
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "Macro" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local instance maskedIidPairMeasurable : MeasurableSpace PairScene := inferInstance
local instance maskedIidMacroMeasurable : MeasurableSpace Macro := inferInstance
local instance maskedIidExtendedMeasurable : MeasurableSpace
    ((Macro × Macro) × (LocalConfiguration base × LocalConfiguration base)) := inferInstance

/-- Select original physical labels by H before observing their rooted positions. -/
def physicalSceneRootedMaskedInputConfiguration {Ω : Type*} {n : ℕ}
    (H : Set M) (coord : M → (ι → ℝ)) (u : M → ℝ)
    (Y : Ω → Fin (n + 1) → M) (v : Ω × (ι → ℝ)) : LocalConfiguration base :=
  ofMaskedTuple base H (fun x ↦ (coord x - v.2, u x)) (Y v.1)

/-- The literal original mask remains measurable jointly with the same root. -/
theorem measurable_physicalSceneRootedMaskedInputConfiguration
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j)) :
    Measurable (physicalSceneRootedMaskedInputConfiguration base H coord u Y) := by
  apply measurable_iff_countingMeasure_comp.mpr
  simp only [physicalSceneRootedMaskedInputConfiguration, countingMeasure_ofMaskedTuple]
  apply Finset.measurable_sum
  intro j _
  have hj : Measurable (fun v : Ω × (ι → ℝ) ↦ Y v.1 j) :=
    (hY j).comp measurable_fst
  exact (Measure.measurable_dirac.comp
    (((hcoord.comp hj).sub measurable_snd).prodMk (hu.comp hj))).ite
      (hH.preimage hj) measurable_const

/-- Masked local counts are bounded by the original full tuple counts with all
original retained multiplicities unchanged. -/
theorem countingMeasure_physicalSceneRootedMaskedInputConfiguration_le
    {Ω : Type*} {n : ℕ} (H : Set M) (coord : M → (ι → ℝ)) (u : M → ℝ)
    (Y : Ω → Fin (n + 1) → M) (v : Ω × (ι → ℝ)) :
    countingMeasure (physicalSceneRootedMaskedInputConfiguration base H coord u Y v) ≤
      countingMeasure (cavityRootedTargetConfiguration base
        (fun w j ↦ (coord (Y w j), u (Y w j))) v) := by
  classical
  simp only [physicalSceneRootedMaskedInputConfiguration, countingMeasure_ofMaskedTuple,
    cavityRootedTargetConfiguration, countingMeasure_ofTuple, cavitySpatialTranslate]
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_rfl
  · exact bot_le

/-- The original Haar count bound also controls the masked cloud. No endpoint
distribution or independence premise is needed for this deterministic estimate. -/
theorem lintegral_physicalSceneRootedMaskedInputConfiguration_sourceWindow_le
    {Ω : Type*} {n : ℕ} (H : Set M) (coord : M → (ι → ℝ)) (u : M → ℝ)
    (Y : Ω → Fin (n + 1) → M) (w : Ω)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ z, countingMeasure
      (physicalSceneRootedMaskedInputConfiguration base H coord u Y (w,z)) (U ×ˢ univ)
      ∂cavityRootMeasure volume D ((n : ℝ) + 1)) ≤ volume U :=
  (lintegral_mono fun z ↦
    countingMeasure_physicalSceneRootedMaskedInputConfiguration_le
      base H coord u Y (w,z) (U ×ˢ univ)).trans
    (lintegral_physicalSceneRootedTargetConfiguration_sourceWindow_le base
      (fun w j ↦ (coord (Y w j), u (Y w j))) w D U hU)

/-- The literal masked original cloud has tight rooted laws from the existing
Haar first-count bound and integer-configuration compact containment. -/
theorem isTightMeasureSet_physicalSceneRootedMaskedInputConfiguration
    {I : Type*} {Ω : I → Type*} [∀ k, MeasurableSpace (Ω k)]
    (m : I → ℕ) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (H : I → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : I → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    (Y : ∀ k, Ω k → Fin (m k + 1) → M)
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j)) (D : I → Set (ι → ℝ)) :
    IsTightMeasureSet (range fun k ↦
      ((P k).prod (cavityRootMeasure volume (D k) ((m k : ℝ) + 1))).map
        (physicalSceneRootedMaskedInputConfiguration base (H k) (coord k) u (Y k))) := by
  apply isTightMeasureSet_of_lintegral_countingMeasure_ball_le _
    (fun n ↦ volume (Metric.ball base.1 ((n + 1 : ℕ) : ℝ)))
    (fun _ ↦ measure_ball_lt_top.ne)
  rintro _ ⟨k, rfl⟩ n
  have hconfig := measurable_physicalSceneRootedMaskedInputConfiguration base
    (H k) (hH k) (coord k) (hcoord k) u hu (Y k) (hY k)
  have hm : Measurable (fun config : LocalConfiguration base ↦
      countingMeasure config (Metric.ball base ((n + 1 : ℕ) : ℝ))) :=
    (Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp measurable_countingMeasure
  rw [lintegral_map hm hconfig]
  let ρ := cavityRootMeasure volume (D k) ((m k : ℝ) + 1)
  have : SFinite ρ := by dsimp only [ρ, cavityRootMeasure]; infer_instance
  have hprod := lintegral_prod (μ := P k) (ν := ρ)
    ((fun config : LocalConfiguration base ↦
      countingMeasure config (Metric.ball base ((n + 1 : ℕ) : ℝ))) ∘
        physicalSceneRootedMaskedInputConfiguration base (H k) (coord k) u (Y k))
    (hm.comp hconfig).aemeasurable
  dsimp only [Function.comp_def] at hprod
  rw [hprod]
  calc
    _ ≤ ∫⁻ w, ∫⁻ z, countingMeasure
        (physicalSceneRootedMaskedInputConfiguration base (H k) (coord k) u (Y k) (w,z))
        (Metric.ball base.1 ((n + 1 : ℕ) : ℝ) ×ˢ univ) ∂ρ ∂P k := by
      apply lintegral_mono
      intro w
      apply lintegral_mono
      intro z
      apply measure_mono
      intro y hy
      have hy' : y ∈ Metric.ball base.1 ((n + 1 : ℕ) : ℝ) ×ˢ
          Metric.ball base.2 ((n + 1 : ℕ) : ℝ) := by
        simpa only [ball_prod_same] using hy
      exact ⟨hy'.1, mem_univ _⟩
    _ ≤ ∫⁻ _ : Ω k, volume (Metric.ball base.1 ((n + 1 : ℕ) : ℝ)) ∂P k := by
      apply lintegral_mono
      intro w
      exact lintegral_physicalSceneRootedMaskedInputConfiguration_sourceWindow_le base
        (H k) (coord k) u (Y k) w (D k) _ Metric.isOpen_ball.measurableSet
    _ = _ := by simp

/-- Keep the exact old macro tags and optimizer plans, replacing only each
input record by its literal original H-masked cloud. -/
def originalIIDMaskedBipartiteMacroObservation
    (cost : M → M → ℝ) (k : ℝ) (n : ℕ) (H : Set M)
    (coord : M → (ι → ℝ)) (u : M → ℝ) (scale : ℝ)
    (w : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) × (ι → ℝ)) : Macro × Macro :=
  let old := originalIIDBipartiteMacroObservation base cost k n H coord u scale w
  ((old.1.1, old.1.2.1,
      physicalSceneRootedMaskedInputConfiguration base H coord u (fun ξ ↦ ξ.1) w),
    (old.2.1, old.2.2.1,
      physicalSceneRootedMaskedInputConfiguration base H coord u (fun ξ ↦ ξ.2) w))

/-- Both original masks are measurable on the unchanged sample/root space. -/
theorem measurable_originalIIDMaskedBipartiteMacroObservation
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ) :
    Measurable (originalIIDMaskedBipartiteMacroObservation base cost k n H coord u scale) := by
  have ho := measurable_originalIIDBipartiteMacroObservation base
    cost hcost k n H hH coord hcoord u hu scale
  have hs := measurable_physicalSceneRootedMaskedInputConfiguration base H hH
    coord hcoord u hu (fun ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M) ↦ ξ.1)
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
  have ht := measurable_physicalSceneRootedMaskedInputConfiguration base H hH
    coord hcoord u hu (fun ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M) ↦ ξ.2)
    (fun j ↦ (measurable_pi_apply j).comp measurable_snd)
  exact (ho.fst.fst.prodMk (ho.fst.snd.fst.prodMk hs)).prodMk
    (ho.snd.fst.prodMk (ho.snd.snd.fst.prodMk ht))

/-- The same two original iid arrays and normalized mass-(n+1) Haar root law
jointly observe both original seed-masked inputs and the unchanged optimizer. -/
def originalIIDMaskedBipartiteMacroLaw
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) : ProbabilityMeasure (Macro × Macro) := by
  let R := haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)
  let D := haarRootCube ι R
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hD : volume D = ENNReal.ofReal ((n : ℝ) + 1) := volume_haarRootCube_radius ι hq hN
  have := isProbabilityMeasure_cavityRootMeasure volume D ((n : ℝ) + 1) hN hD
  let P := (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  exact ⟨(P.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (originalIIDMaskedBipartiteMacroObservation base cost k n H coord u (2 * R)),
    Measure.isProbabilityMeasure_map
      (measurable_originalIIDMaskedBipartiteMacroObservation base cost hcost k n H hH
        coord hcoord u hu (2 * R)).aemeasurable⟩

/-- Forgetting the cloud coordinates preserves both exact original macro tags
and every coordinate of the same original optimizer plans. -/
theorem originalIIDMaskedBipartiteMacroObservation_tag_plans
    (cost : M → M → ℝ) (k : ℝ) (n : ℕ) (H : Set M)
    (coord : M → (ι → ℝ)) (u : M → ℝ) (scale : ℝ)
    (w : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) × (ι → ℝ)) :
    let s := originalIIDMaskedBipartiteMacroObservation base cost k n H coord u scale w
    let old := originalIIDBipartiteMacroObservation base cost k n H coord u scale w
    ((s.1.1,s.1.2.1),(s.2.1,s.2.2.1)) =
      ((old.1.1,old.1.2.1),(old.2.1,old.2.2.1)) := rfl

/-- The actual masked two-input joint laws are tight for arbitrary measurable
varying costs, from the old original optimizer tightness and Haar count bounds. -/
theorem isTightMeasureSet_originalIIDMaskedBipartiteMacroLaw_varying_cost
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) :
    IsTightMeasureSet (range fun n ↦
      (originalIIDMaskedBipartiteMacroLaw base μ ν hq (cost n) (hcost n) (k n) n H hH
        (coord n) (hcoord n) u hu : Measure (Macro × Macro))) := by
  let Penv := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  let radius := fun n : ℕ ↦ haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)
  let D := fun n ↦ haarRootCube ι (radius n)
  let P := fun n ↦ (Penv n).prod (cavityRootMeasure volume (D n) ((n : ℝ) + 1))
  let old := fun n ↦ originalIIDBipartiteMacroObservation base
    (cost n) (k n) n H (coord n) u (2 * radius n)
  let source := fun n ↦ physicalSceneRootedMaskedInputConfiguration base H (coord n) u
    (fun ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M) ↦ ξ.1)
  let target := fun n ↦ physicalSceneRootedMaskedInputConfiguration base H (coord n) u
    (fun ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M) ↦ ξ.2)
  have hold (n : ℕ) : Measurable (old n) :=
    measurable_originalIIDBipartiteMacroObservation base
      (cost n) (hcost n) (k n) n H hH (coord n) (hcoord n) u hu (2 * radius n)
  have hsource (n : ℕ) : Measurable (source n) :=
    measurable_physicalSceneRootedMaskedInputConfiguration base H hH (coord n) (hcoord n)
      u hu _ (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
  have htarget (n : ℕ) : Measurable (target n) :=
    measurable_physicalSceneRootedMaskedInputConfiguration base H hH (coord n) (hcoord n)
      u hu _ (fun j ↦ (measurable_pi_apply j).comp measurable_snd)
  have hOld : IsTightMeasureSet (range fun n ↦ (P n).map (old n)) :=
    isTightMeasureSet_originalIIDBipartiteMacroLaw_varying_cost base
      μ ν hq cost hcost k H hH coord hcoord u hu
  have hSource : IsTightMeasureSet (range fun n ↦ (P n).map (source n)) :=
    isTightMeasureSet_physicalSceneRootedMaskedInputConfiguration base id Penv
      (fun _ ↦ H) (fun _ ↦ hH) coord hcoord u hu
      (fun _ ξ ↦ ξ.1) (fun _ j ↦ (measurable_pi_apply j).comp measurable_fst) D
  have hTarget : IsTightMeasureSet (range fun n ↦ (P n).map (target n)) :=
    isTightMeasureSet_physicalSceneRootedMaskedInputConfiguration base id Penv
      (fun _ ↦ H) (fun _ ↦ hH) coord hcoord u hu
      (fun _ ξ ↦ ξ.2) (fun _ j ↦ (measurable_pi_apply j).comp measurable_snd) D
  have hInput := isTightMeasureSet_original_joint_of_marginals P source target
    hsource htarget hSource hTarget
  have hJoint := isTightMeasureSet_original_joint_of_marginals P old
    (fun n w ↦ (source n w,target n w)) hold
    (fun n ↦ (hsource n).prodMk (htarget n)) hOld hInput
  let replace : (Macro × Macro) × (LocalConfiguration base × LocalConfiguration base) →
      Macro × Macro := fun z ↦
    ((z.1.1.1,z.1.1.2.1,z.2.1),(z.1.2.1,z.1.2.2.1,z.2.2))
  have hreplace : Continuous replace :=
    (continuous_fst.fst.fst.prodMk
      (continuous_fst.fst.snd.fst.prodMk continuous_snd.fst)).prodMk
      (continuous_fst.snd.fst.prodMk
        (continuous_fst.snd.snd.fst.prodMk continuous_snd.snd))
  have hmreplace : Measurable replace :=
    (measurable_fst.fst.fst.prodMk
      (measurable_fst.fst.snd.fst.prodMk measurable_snd.fst)).prodMk
      (measurable_fst.snd.fst.prodMk
        (measurable_fst.snd.snd.fst.prodMk measurable_snd.snd))
  have hT := hJoint.map hreplace
  apply hT.subset
  rintro _ ⟨n,rfl⟩
  refine ⟨_, ⟨n,rfl⟩, ?_⟩
  rw [Measure.map_map hmreplace
    ((hold n).prodMk ((hsource n).prodMk (htarget n)))]
  rfl

/-- All countably many original masked two-input frames retain one common
weak sample subsequence of the same original finite optimizers and root laws. -/
theorem exists_originalIID_common_masked_bipartite_macro_subsequence_varying_cost
    (axes : ℕ → Type*) [∀ j, Fintype (axes j)]
    (hq : ∀ j, 0 < Fintype.card (axes j))
    (base : ∀ j, (axes j → ℝ) × ℝ)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : ℕ → Set M) (hH : ∀ j, MeasurableSet (H j))
    (coord : ∀ j, ℕ → M → (axes j → ℝ)) (hcoord : ∀ j n, Measurable (coord j n))
    (u : M → ℝ) (hu : Measurable u) :
    let T := fun j ↦ (axes j → ℝ) ×
      (CavityLocalScene ((axes j → ℝ) × ℝ) ((axes j → ℝ) × ℝ) ×
        LocalConfiguration (base j))
    let laws := fun j n ↦ originalIIDMaskedBipartiteMacroLaw (base j) μ ν (hq j)
      (cost n) (hcost n) (k n) n (H j) (hH j) (coord j n) (hcoord j n) u hu
    ∃ Q : ∀ j, ProbabilityMeasure (T j × T j), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j, Tendsto (fun n ↦ laws j (φ n)) atTop (𝓝 (Q j)) := by
  intro T laws
  have htight (j : ℕ) : IsTightMeasureSet
      (range fun v : ℕ × ℕ ↦ (laws j v.2 : Measure (T j × T j))) := by
    have ht := isTightMeasureSet_originalIIDMaskedBipartiteMacroLaw_varying_cost
      (base j) μ ν (hq j) cost hcost k (H j) (hH j) (coord j) (hcoord j) u hu
    convert ht using 1
    ext ρ
    constructor
    · rintro ⟨⟨ℓ,n⟩,rfl⟩
      exact ⟨n,rfl⟩
    · rintro ⟨n,rfl⟩
      exact ⟨(0,n),rfl⟩
  obtain ⟨Q,φ,hφ,hinner,_⟩ := exists_common_iterated_probabilityMeasure_subseq_of_isTight
    (fun j (_ : ℕ) n ↦ laws j n) htight
  exact ⟨fun j ↦ Q j 0,φ 0,hφ 0,fun j ↦ hinner j 0⟩

end OTSelector.Reconstruction

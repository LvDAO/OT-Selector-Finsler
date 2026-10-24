import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedClockWindows
import OTSelector.MeasureTheory.IteratedWeakOpenCollarNull

/-! Actual original clock collars remove full-plan boundary mass in both weak limits. -/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)
local instance maskedClockNullLimitStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance maskedClockNullLimitConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance maskedClockNullLimitConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance maskedClockNullLimitConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance maskedClockNullLimitPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "Edge" => (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Only original expected global clock-collar masses are assumed. Their
vanishing removes the corresponding clock set from the SAME complete limiting
plans, with all actual random restricted columns retained. -/
theorem ae_full_original_clock_null_of_iterated_actual_masked_scene
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (Penv : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (Penv n)]
    (Γp Γm : ∀ (_ℓ n : ℕ), Ωn n → Measure (M × M))
    [∀ ℓ n w, IsFiniteMeasure (Γp ℓ n w)]
    [∀ ℓ n w, IsFiniteMeasure (Γm ℓ n w)]
    (hp : ∀ ℓ n, Measurable (Γp ℓ n)) (hm : ∀ ℓ n, Measurable (Γm ℓ n))
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (scale : ℕ → ℝ)
    (Y : ∀ n, Ωn n → Fin (n + 1) → M)
    (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (rootDomain : ℕ → Set (ι → ℝ))
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1))
    (B : Set (ℝ × ℝ)) (hB : MeasurableSet B)
    (collar : ℕ → Set (ℝ × ℝ)) (hcollar : ∀ m, IsOpen (collar m))
    (hsub : ∀ m, B ⊆ collar m)
    (error : ℕ → ℝ≥0∞) (herror : Tendsto error atTop (𝓝 0))
    (hCp : ∀ m ℓ n, (∫⁻ w, Γp ℓ n w
      ((fun p : M × M ↦ (u p.1, u p.2)) ⁻¹' collar m) ∂Penv n) ≤ error m)
    (hCm : ∀ m ℓ n, (∫⁻ w, Γm ℓ n w
      ((fun p : M × M ↦ (u p.1, u p.2)) ⁻¹' collar m) ∂Penv n) ≤ error m) :
    let laws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦
      physicalSceneRootedMaskedMacroscopicSceneLaw base (Penv n) (Γp ℓ n) (Γm ℓ n)
        (hp ℓ n) (hm ℓ n) H hH E hE (coord n) (hcoord n) u hu (scale n)
        (Y n) (hY n) (rootDomain n) (hrootDomain n)
    ∀ (Q : ℕ → ProbabilityMeasure JointScene) (R : ProbabilityMeasure JointScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) → ∀ ψ : ℕ → ℕ,
      Tendsto ψ atTop atTop →
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R) →
      ∀ᵐ s ∂(R : Measure JointScene),
        (LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure Edge)
          {e | (e.1.2, e.2.2) ∈ B} = 0 := by
  dsimp only
  intro Q R φ hφ ψ hψ hinner houter
  let laws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦
    physicalSceneRootedMaskedMacroscopicSceneLaw base (Penv n) (Γp ℓ n) (Γm ℓ n)
      (hp ℓ n) (hm ℓ n) H hH E hE (coord n) (hcoord n) u hu (scale n)
      (Y n) (hY n) (rootDomain n) (hrootDomain n)
  let plan : JointScene → LocalFiniteMeasure Edge :=
    fun s ↦ LocalFiniteMeasure.cavityAverage s.1.2.1
  have hplan : Continuous plan := LocalFiniteMeasure.continuous_cavityAverage.comp
    continuous_fst.snd.fst
  have hwindow (U : Set (ι → ℝ)) (hU : IsOpen U) (hUf : volume U ≠ ⊤) :
      ∀ᵐ s ∂(R : Measure JointScene),
        (plan s : Measure Edge) (physicalSceneRootedClockWindow U B) = 0 := by
    apply ae_physicalScenePlan_null_of_iterated_open_collar_bounds
      laws Q R φ hφ ψ hψ hinner houter plan hplan
      (measurableSet_physicalSceneRootedClockWindow hU.measurableSet hB)
      (fun m ↦ physicalSceneRootedClockWindow U (collar m))
      (fun m ↦ isOpen_physicalSceneRootedClockWindow hU (hcollar m))
      (fun m e he ↦ ⟨he.1, hsub m he.2⟩)
      (fun m ↦ volume U * error m) ?_ ?_
    · simpa only [mul_zero] using ENNReal.Tendsto.const_mul herror (Or.inr hUf)
    · intro m ℓ n
      exact lintegral_physicalSceneRootedMaskedMacroscopicSceneLaw_fullClock_le base
        (Penv n) (Γp ℓ n) (Γm ℓ n) (hp ℓ n) (hm ℓ n) H hH E hE
        (coord n) (hcoord n) u hu (scale n) (Y n) (hY n)
        (rootDomain n) (hrootDomain n) U hU hUf (collar m) (hcollar m)
        (error m) (hCp m ℓ n) (hCm m ℓ n)
  have hall : ∀ᵐ s ∂(R : Measure JointScene), ∀ n : ℕ,
      (plan s : Measure Edge)
        (physicalSceneRootedClockWindow (Metric.ball 0 ((n : ℝ) + 1)) B) = 0 :=
    ae_all_iff.mpr fun n ↦ hwindow _ Metric.isOpen_ball measure_ball_ne_top
  filter_upwards [hall] with s hs
  change (plan s : Measure Edge) {e | (e.1.2, e.2.2) ∈ B} = 0
  have hcover : {e : Edge | (e.1.2, e.2.2) ∈ B} ⊆
      ⋃ n : ℕ, physicalSceneRootedClockWindow (Metric.ball 0 ((n : ℝ) + 1)) B := by
    intro e he
    obtain ⟨n, hn⟩ := exists_nat_gt ‖e.1.1‖
    refine mem_iUnion.mpr ⟨n, ?_, he⟩
    simpa only [Metric.mem_ball, dist_zero_right] using hn.trans (lt_add_one (n : ℝ))
  apply measure_mono_null hcover
  exact measure_iUnion_null hs
end OTSelector.Reconstruction

import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedClockGap
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedJoint
import OTSelector.Probability.DirichletReference

/-!
# Original positive full clock gap in the same actual masked joint limits

The exact full/countable projection forgets only the actual auxiliary masks and
macroscopic tag. Original physical support separation and uniform true global
energy then produce the same positive clock gap for the full arithmetic average,
through the fixed-tilt sample limit and the subsequent outer tilt-index limit.
-/

open TopologicalSpace Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {ι M : Type*} [Fintype ι] [MetricSpace M] [MeasurableSpace M]
  [BorelSpace M] [SecondCountableTopology M]
variable (base : (ι → ℝ) × ℝ)

local instance actualMaskedMeasurableClockStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance actualMaskedMeasurableClockConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance actualMaskedMeasurableClockConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace (base := base)
local instance actualMaskedMeasurableClockConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace (base := base)
local instance actualMaskedMeasurableClockPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local notation "Point" => (ι → ℝ) × ℝ
local notation "Edge" => ((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "CountableScene" => PairScene × LocalConfiguration base
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

theorem ae_actualAllocationRootedScene_limit_clock_gap_of_measurable_support
    {Ωn : ℕ → Type*} [∀ k, MeasurableSpace (Ωn k)]
    (m : ℕ → ℕ) (P : ∀ k, Measure (Ωn k)) [∀ k, IsProbabilityMeasure (P k)]
    (μ ν : Measure M) [IsFiniteMeasure μ]
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {gap : ℝ} (hgap : 0 < gap) (hdist : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (aplus aminus : ∀ k, Ωn k → M → Fin (m k + 1) → ℝ)
    (hplus : ∀ k j, Measurable (fun z : Ωn k × M ↦ aplus k z.1 z.2 j))
    (hminus : ∀ k j, Measurable (fun z : Ωn k × M ↦ aminus k z.1 z.2 j))
    (Y : ∀ k, Ωn k → Fin (m k + 1) → M)
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (hYlaw : ∀ k j, (P k).map (fun w ↦ Y k w j) = ν)
    (p : ∀ k, Ωn k → Fin (m k + 1) → ℝ)
    (hfeasplus : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (aplus k w))
    (hfeasminus : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (aminus k w))
    (H : ℕ → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (scale : ℕ → ℝ) (hscale : ∀ k, 0 < scale k)
    (hscaleTop : Tendsto scale atTop atTop)
    (N : ℕ → ℝ) (hN : ∀ k, 0 < N k)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ k, volume (D k) = ENNReal.ofReal (N k))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergyplus : ∀ k, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale k * (dist e.1 (Y k w e.2) - u (Y k w e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aplus k w) ∂P k) ≤ C)
    (henergyminus : ∀ k, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale k * (dist e.1 (Y k w e.2) - u (Y k w e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aminus k w) ∂P k) ≤ C)
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (hweak : Tendsto (fun k ↦ actualAllocationRootedSceneLaw (P k) μ (aplus k) (aminus k)
      (hplus k) (hminus k) (Y k) (hY k) (H k) (hH k) (coord k) (hcoord k)
      u hu.continuous.measurable (N k) (hN k) (D k) (hD k)) atTop (𝓝 Q)) :
    ∀ᵐ scene ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
      (∀ᵐ e ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), gap / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), gap / 2 ≤ e.2.2 - e.1.2) := by
  let Γplus := fun k ↦ physicalSceneGlobalAllocationFamily μ (aplus k) (Y k)
  let Γminus := fun k ↦ physicalSceneGlobalAllocationFamily μ (aminus k) (Y k)
  have hYB (k : ℕ) : ∀ᵐ w ∂P k, ∀ j, Y k w j ∈ B := by
    apply ae_all_iff.mpr
    intro j
    apply ae_of_ae_map (p := fun y ↦ y ∈ B) (hY k j).aemeasurable
    simpa only [hYlaw k j] using hνB
  have hcarriedplus (k : ℕ) : ∀ᵐ w ∂P k, ∀ᵐ e ∂Γplus k w,
      e.1 ∈ A ∧ e.2 ∈ B :=
    ae_physicalSceneGlobalAllocationFamily_carried (P k) μ (aplus k) (Y k) (p k)
      (hfeasplus k) hA hB hμA (hYB k)
  have hcarriedminus (k : ℕ) : ∀ᵐ w ∂P k, ∀ᵐ e ∂Γminus k w,
      e.1 ∈ A ∧ e.2 ∈ B :=
    ae_physicalSceneGlobalAllocationFamily_carried (P k) μ (aminus k) (Y k) (p k)
      (hfeasminus k) hA hB hμA (hYB k)
  let energy := fun k (e : M × M) ↦
    ENNReal.ofReal (scale k * (dist e.1 e.2 - u e.2 + u e.1))
  have hem (k : ℕ) : Measurable (energy k) :=
    ((((continuous_fst.dist continuous_snd).sub (hu.continuous.comp continuous_snd)).add
      (hu.continuous.comp continuous_fst)).const_mul (scale k)).measurable.ennreal_ofReal
  have hep (k : ℕ) : (∫⁻ w, ∫⁻ e, energy k e ∂Γplus k w ∂P k) ≤ C := by
    rw [lintegral_physicalSceneGlobalAllocationFamily_eq (P k) μ (aplus k) (Y k) (p k)
      (hfeasplus k) (fun _ ↦ energy k) (fun _ ↦ hem k)]
    exact henergyplus k
  have hem' (k : ℕ) : (∫⁻ w, ∫⁻ e, energy k e ∂Γminus k w ∂P k) ≤ C := by
    rw [lintegral_physicalSceneGlobalAllocationFamily_eq (P k) μ (aminus k) (Y k) (p k)
      (hfeasminus k) (fun _ ↦ energy k) (fun _ ↦ hem k)]
    exact henergyminus k
  have hlegal := ae_physicalSceneRootedLocalScene_limit_clock_legal P Γplus Γminus
    (fun k ↦ measurable_physicalSceneGlobalAllocationFamily μ (aplus k) (hplus k) (Y k) (hY k))
    (fun k ↦ measurable_physicalSceneGlobalAllocationFamily μ (aminus k) (hminus k) (Y k) (hY k))
    hgap hdist hcarriedplus hcarriedminus H hH coord hcoord hu scale hscale hscaleTop
    N hN D hD C hC hep hem' Q hweak
  exact hlegal


theorem ae_iterated_actualAllocationRootedCountableScene_clock_gap_of_support_gap_of_measurable_support
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ ν : Measure M) [IsFiniteMeasure μ]
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {σ : ℝ} (hσ : 0 < σ) (hdist : ∀ x ∈ A, ∀ y ∈ B, σ ≤ dist x y)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (aplus aminus : ∀ (_k n : ℕ), Ω n → M → Fin (m n + 1) → ℝ)
    (hplus : ∀ k n j, Measurable (fun z : Ω n × M ↦ aplus k n z.1 z.2 j))
    (hminus : ∀ k n j, Measurable (fun z : Ω n × M ↦ aminus k n z.1 z.2 j))
    (Y : ∀ n, Ω n → Fin (m n + 1) → M)
    (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (hYlaw : ∀ n j, (P n).map (fun w ↦ Y n w j) = ν)
    (p : ∀ n, Ω n → Fin (m n + 1) → ℝ)
    (hfeasplus : ∀ k n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (aplus k n w))
    (hfeasminus : ∀ k n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (aminus k n w))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergyplus : ∀ k n, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale n * (dist e.1 (Y n w e.2) - u (Y n w e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aplus k n w) ∂P n) ≤ C)
    (henergyminus : ∀ k n, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale n * (dist e.1 (Y n w e.2) - u (Y n w e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aminus k n w) ∂P n) ≤ C)
    (Q : ℕ → ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, StrictMono (φ k))
    (hinner : ∀ k, Tendsto (fun n ↦
      actualAllocationRootedCountableSceneLaw base (P (φ k n)) μ
        (aplus k (φ k n)) (aminus k (φ k n)) (hplus k (φ k n)) (hminus k (φ k n))
        (Y (φ k n)) (hY (φ k n)) (H (φ k n)) (hH (φ k n))
        (coord (φ k n)) (hcoord (φ k n)) u hu.continuous.measurable
        (D (φ k n)) (hD (φ k n))) atTop (𝓝 (Q k)))
    (R : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))
    (ψ : ℕ → ℕ) (houter : Tendsto (Q ∘ ψ) atTop (𝓝 R)) :
    ∀ᵐ s ∂(R : Measure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
      (∀ᵐ e ∂(s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
        σ / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
        σ / 2 ≤ e.2.2 - e.1.2) := by
  let Qpair := fun k ↦ (Q k).map (f := Prod.fst) measurable_fst.aemeasurable
  have hweakpair (k : ℕ) : Tendsto (fun n ↦ actualAllocationRootedSceneLaw
      (P (φ k n)) μ (aplus k (φ k n)) (aminus k (φ k n))
      (hplus k (φ k n)) (hminus k (φ k n)) (Y (φ k n)) (hY (φ k n))
      (H (φ k n)) (hH (φ k n)) (coord (φ k n)) (hcoord (φ k n))
      u hu.continuous.measurable ((m (φ k n) : ℝ) + 1) (by positivity)
      (D (φ k n)) (hD (φ k n))) atTop (𝓝 (Qpair k)) := by
    have hw := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n ↦ actualAllocationRootedCountableSceneLaw base (P (φ k n)) μ
        (aplus k (φ k n)) (aminus k (φ k n)) (hplus k (φ k n)) (hminus k (φ k n))
        (Y (φ k n)) (hY (φ k n)) (H (φ k n)) (hH (φ k n))
        (coord (φ k n)) (hcoord (φ k n)) u hu.continuous.measurable
        (D (φ k n)) (hD (φ k n))) (Q k) (hinner k) continuous_fst
    simpa only [map_actualAllocationRootedCountableSceneLaw_pair] using hw
  have hσpair (k : ℕ) := ae_actualAllocationRootedScene_limit_clock_gap_of_measurable_support
    (fun n ↦ m (φ k n)) (fun n ↦ P (φ k n)) μ ν hA hB hσ hdist hμA hνB
    (fun n ↦ aplus k (φ k n)) (fun n ↦ aminus k (φ k n))
    (fun n ↦ hplus k (φ k n)) (fun n ↦ hminus k (φ k n))
    (fun n ↦ Y (φ k n)) (fun n ↦ hY (φ k n)) (fun n ↦ hYlaw (φ k n))
    (fun n ↦ p (φ k n)) (fun n ↦ hfeasplus k (φ k n)) (fun n ↦ hfeasminus k (φ k n))
    (fun n ↦ H (φ k n)) (fun n ↦ hH (φ k n))
    (fun n ↦ coord (φ k n)) (fun n ↦ hcoord (φ k n)) hu
    (fun n ↦ scale (φ k n)) (fun n ↦ hscale (φ k n))
    (hscaleTop.comp (hφ k).tendsto_atTop)
    (fun n ↦ (m (φ k n) : ℝ) + 1) (fun _ ↦ by positivity)
    (fun n ↦ D (φ k n)) (fun n ↦ hD (φ k n)) C hC
    (fun n ↦ henergyplus k (φ k n)) (fun n ↦ henergyminus k (φ k n))
    (Qpair k) (hweakpair k)
  have hσinner (k : ℕ) : ∀ᵐ s ∂(Q k : Measure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
      (∀ᵐ e ∂(s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
        σ / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
        σ / 2 ≤ e.2.2 - e.1.2) :=
    ae_of_ae_map (μ := (Q k : Measure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)))
      (f := Prod.fst)
      (p := fun s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
        (∀ᵐ e ∂(s.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
          σ / 2 ≤ e.2.2 - e.1.2) ∧
        (∀ᵐ e ∂(s.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
          σ / 2 ≤ e.2.2 - e.1.2)) measurable_fst.aemeasurable (hσpair k)
  let K : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) :=
    {e | σ / 2 ≤ e.2.2 - e.1.2}
  have hK : IsClosed K := isClosed_le continuous_const (continuous_snd.snd.sub continuous_fst.snd)
  have hp := ae_localFiniteMeasure_carried_of_weak_tendsto R (Q ∘ ψ) houter
    (fun s ↦ s.1.1) continuous_fst.fst hK
    (fun k ↦ (hσinner (ψ k)).mono fun _ h ↦ h.1)
  have hm := ae_localFiniteMeasure_carried_of_weak_tendsto R (Q ∘ ψ) houter
    (fun s ↦ s.1.2) continuous_fst.snd hK
    (fun k ↦ (hσinner (ψ k)).mono fun _ h ↦ h.2)
  exact hp.and hm




theorem ae_iterated_actualAllocationRootedMaskedMacroscopicScene_full_average_clock_gap_of_measurable_support
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ ν : Measure M) [IsFiniteMeasure μ]
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {σ : ℝ} (hσ : 0 < σ) (hdist : ∀ x ∈ A, ∀ y ∈ B, σ ≤ dist x y)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (aplus aminus : ∀ (_ℓ n : ℕ), Ω n → M → Fin (m n + 1) → ℝ)
    (hplus : ∀ ℓ n j, Measurable (fun z : Ω n × M ↦ aplus ℓ n z.1 z.2 j))
    (hminus : ∀ ℓ n j, Measurable (fun z : Ω n × M ↦ aminus ℓ n z.1 z.2 j))
    (Y : ∀ n, Ω n → Fin (m n + 1) → M)
    (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (hYlaw : ∀ n j, (P n).map (fun w ↦ Y n w j) = ν)
    (p : ∀ n, Ω n → Fin (m n + 1) → ℝ)
    (hfeasplus : ∀ ℓ n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (aplus ℓ n w))
    (hfeasminus : ∀ ℓ n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (aminus ℓ n w))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (E : ℕ → ℕ → Set (M × M)) (hE : ∀ ℓ n, MeasurableSet (E ℓ n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (costScale : ℕ → ℝ) (hscale : ∀ n, 0 < costScale n)
    (hscaleTop : Tendsto costScale atTop atTop) (macroScale : ℕ → ℝ)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergyplus : ∀ ℓ n, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (costScale n * (dist e.1 e.2 - u e.2 + u e.1))
        ∂physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (Y n) w ∂P n) ≤ C)
    (henergyminus : ∀ ℓ n, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (costScale n * (dist e.1 e.2 - u e.2 + u e.1))
        ∂physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (Y n) w ∂P n) ≤ C)
    (Q : ℕ → ProbabilityMeasure JointScene)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, StrictMono (φ ℓ))
    (hinner : ∀ ℓ, Tendsto (fun n ↦
      actualAllocationRootedMaskedMacroscopicSceneLaw base (P (φ ℓ n)) μ
        (aplus ℓ (φ ℓ n)) (aminus ℓ (φ ℓ n)) (hplus ℓ (φ ℓ n)) (hminus ℓ (φ ℓ n))
        (Y (φ ℓ n)) (hY (φ ℓ n)) (H (φ ℓ n)) (hH (φ ℓ n))
        (E ℓ (φ ℓ n)) (hE ℓ (φ ℓ n)) (coord (φ ℓ n)) (hcoord (φ ℓ n))
        u hu.continuous.measurable (macroScale (φ ℓ n)) (D (φ ℓ n)) (hD (φ ℓ n)))
      atTop (𝓝 (Q ℓ)))
    (R : ProbabilityMeasure JointScene) (ψ : ℕ → ℕ)
    (houter : Tendsto (Q ∘ ψ) atTop (𝓝 R)) :
    ∀ᵐ s ∂(R : Measure JointScene),
      ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure Edge),
        σ / 2 ≤ e.2.2 - e.1.2 := by
  let energy := fun n (e : M × M) ↦
    ENNReal.ofReal (costScale n * (dist e.1 e.2 - u e.2 + u e.1))
  have hem (n : ℕ) : Measurable (energy n) :=
    ((((continuous_fst.dist continuous_snd).sub (hu.continuous.comp continuous_snd)).add
      (hu.continuous.comp continuous_fst)).const_mul (costScale n)).measurable.ennreal_ofReal
  have herawplus (ℓ n : ℕ) : (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (costScale n * (dist e.1 (Y n w e.2) - u (Y n w e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aplus ℓ n w) ∂P n) ≤ C := by
    rw [← lintegral_physicalSceneGlobalAllocationFamily_eq (P n) μ (aplus ℓ n)
      (Y n) (p n) (hfeasplus ℓ n) (fun _ ↦ energy n) (fun _ ↦ hem n)]
    exact henergyplus ℓ n
  have herawminus (ℓ n : ℕ) : (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (costScale n * (dist e.1 (Y n w e.2) - u (Y n w e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aminus ℓ n w) ∂P n) ≤ C := by
    rw [← lintegral_physicalSceneGlobalAllocationFamily_eq (P n) μ (aminus ℓ n)
      (Y n) (p n) (hfeasminus ℓ n) (fun _ ↦ energy n) (fun _ ↦ hem n)]
    exact henergyminus ℓ n
  let Qcount := fun ℓ ↦ (Q ℓ).map
    (f := fun s : JointScene ↦ s.1.2) measurable_fst.snd.aemeasurable
  let Rcount := R.map (f := fun s : JointScene ↦ s.1.2) measurable_fst.snd.aemeasurable
  have hinnerCount (ℓ : ℕ) : Tendsto (fun n ↦
      actualAllocationRootedCountableSceneLaw base (P (φ ℓ n)) μ
        (aplus ℓ (φ ℓ n)) (aminus ℓ (φ ℓ n)) (hplus ℓ (φ ℓ n)) (hminus ℓ (φ ℓ n))
        (Y (φ ℓ n)) (hY (φ ℓ n)) (H (φ ℓ n)) (hH (φ ℓ n))
        (coord (φ ℓ n)) (hcoord (φ ℓ n)) u hu.continuous.measurable
        (D (φ ℓ n)) (hD (φ ℓ n))) atTop (𝓝 (Qcount ℓ)) := by
    have hw := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n ↦ actualAllocationRootedMaskedMacroscopicSceneLaw base (P (φ ℓ n)) μ
        (aplus ℓ (φ ℓ n)) (aminus ℓ (φ ℓ n)) (hplus ℓ (φ ℓ n)) (hminus ℓ (φ ℓ n))
        (Y (φ ℓ n)) (hY (φ ℓ n)) (H (φ ℓ n)) (hH (φ ℓ n))
        (E ℓ (φ ℓ n)) (hE ℓ (φ ℓ n)) (coord (φ ℓ n)) (hcoord (φ ℓ n))
        u hu.continuous.measurable (macroScale (φ ℓ n)) (D (φ ℓ n)) (hD (φ ℓ n)))
      (Q ℓ) (hinner ℓ) continuous_fst.snd
    simpa only [map_actualAllocationRootedMaskedMacroscopicSceneLaw_countable] using hw
  have houterCount : Tendsto (Qcount ∘ ψ) atTop (𝓝 Rcount) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (Q ∘ ψ) R houter continuous_fst.snd
  have hcount := ae_iterated_actualAllocationRootedCountableScene_clock_gap_of_support_gap_of_measurable_support
    base m P μ ν hA hB hσ hdist hμA hνB aplus aminus hplus hminus Y hY hYlaw p
    hfeasplus hfeasminus H hH coord hcoord hu costScale hscale hscaleTop D hD C hC
    herawplus herawminus Qcount φ hφ hinnerCount Rcount ψ houterCount
  have hfull : ∀ᵐ s ∂(R : Measure JointScene),
      (∀ᵐ e ∂(s.1.2.1.1 : Measure Edge), σ / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(s.1.2.1.2 : Measure Edge), σ / 2 ≤ e.2.2 - e.1.2) :=
    ae_of_ae_map (μ := (R : Measure JointScene))
      (f := fun s : JointScene ↦ s.1.2)
      (p := fun s : CountableScene ↦
        (∀ᵐ e ∂(s.1.1 : Measure Edge), σ / 2 ≤ e.2.2 - e.1.2) ∧
        (∀ᵐ e ∂(s.1.2 : Measure Edge), σ / 2 ≤ e.2.2 - e.1.2))
      measurable_fst.snd.aemeasurable hcount
  filter_upwards [hfull] with s hs
  rw [LocalFiniteMeasure.coe_cavityAverage]
  apply Measure.ae_smul_measure
  exact ae_add_measure_iff.mpr hs



theorem ae_iterated_original_iid_actualMaskedMacroscopicScene_full_average_clock_gap_of_measurable_support
    (m : ℕ → ℕ) (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {σ : ℝ} (hσ : 0 < σ) (hdist : ∀ x ∈ A, ∀ y ∈ B, σ ≤ dist x y)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (aplus aminus : ∀ (_ℓ n : ℕ),
      ((Fin (m n + 1) → M) × (Fin (m n + 1) → ℝ)) → M → Fin (m n + 1) → ℝ)
    (hplus : ∀ ℓ n j, Measurable (fun z :
      ((Fin (m n + 1) → M) × (Fin (m n + 1) → ℝ)) × M ↦ aplus ℓ n z.1 z.2 j))
    (hminus : ∀ ℓ n j, Measurable (fun z :
      ((Fin (m n + 1) → M) × (Fin (m n + 1) → ℝ)) × M ↦ aminus ℓ n z.1 z.2 j))
    (hfeasplus : ∀ ℓ n, ∀ᵐ w ∂((Measure.pi (fun _ : Fin (m n + 1) ↦ ν)).prod
      (dirichletOne (m n))), IsSemidiscreteAllocation μ w.2 (aplus ℓ n w))
    (hfeasminus : ∀ ℓ n, ∀ᵐ w ∂((Measure.pi (fun _ : Fin (m n + 1) ↦ ν)).prod
      (dirichletOne (m n))), IsSemidiscreteAllocation μ w.2 (aminus ℓ n w))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (E : ℕ → ℕ → Set (M × M)) (hE : ∀ ℓ n, MeasurableSet (E ℓ n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (Energy : ℝ≥0∞) (hEnergy : Energy ≠ ⊤)
    (henergyplus : ∀ ℓ n, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale n ^ 2 * (dist e.1 e.2 - u e.2 + u e.1))
        ∂physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (m n + 1) ↦ ν)).prod (dirichletOne (m n)))) ≤ Energy)
    (henergyminus : ∀ ℓ n, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale n ^ 2 * (dist e.1 e.2 - u e.2 + u e.1))
        ∂physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (m n + 1) ↦ ν)).prod (dirichletOne (m n)))) ≤ Energy)
    (Q : ℕ → ProbabilityMeasure JointScene)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, StrictMono (φ ℓ))
    (hinner : ∀ ℓ, Tendsto (fun n ↦
      actualAllocationRootedMaskedMacroscopicSceneLaw base
        ((Measure.pi (fun _ : Fin (m (φ ℓ n) + 1) ↦ ν)).prod (dirichletOne (m (φ ℓ n)))) μ
        (aplus ℓ (φ ℓ n)) (aminus ℓ (φ ℓ n)) (hplus ℓ (φ ℓ n)) (hminus ℓ (φ ℓ n))
        (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
        (H (φ ℓ n)) (hH (φ ℓ n)) (E ℓ (φ ℓ n)) (hE ℓ (φ ℓ n))
        (coord (φ ℓ n)) (hcoord (φ ℓ n)) u hu.continuous.measurable
        (scale (φ ℓ n)) (D (φ ℓ n)) (hD (φ ℓ n))) atTop (𝓝 (Q ℓ)))
    (R : ProbabilityMeasure JointScene) (ψ : ℕ → ℕ)
    (houter : Tendsto (Q ∘ ψ) atTop (𝓝 R)) :
    ∀ᵐ s ∂(R : Measure JointScene),
      ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure Edge),
        σ / 2 ≤ e.2.2 - e.1.2 := by
  have hYlaw (n : ℕ) (j : Fin (m n + 1)) :
      (((Measure.pi (fun _ : Fin (m n + 1) ↦ ν)).prod (dirichletOne (m n))).map
        (fun w ↦ w.1 j)) = ν := by
    calc
      _ = (Measure.pi (fun _ : Fin (m n + 1) ↦ ν)).map (fun y ↦ y j) := by
        simpa only [Measure.map_fst_prod, measure_univ, one_smul, Function.comp_def]
          using (Measure.map_map
            (μ := (Measure.pi (fun _ : Fin (m n + 1) ↦ ν)).prod (dirichletOne (m n)))
            (measurable_pi_apply j) measurable_fst).symm
      _ = ν := (measurePreserving_eval (fun _ : Fin (m n + 1) ↦ ν) j).map_eq
  have hscale2 : Tendsto (fun n ↦ scale n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).comp hscaleTop
  exact ae_iterated_actualAllocationRootedMaskedMacroscopicScene_full_average_clock_gap_of_measurable_support
    base m (fun n ↦ (Measure.pi (fun _ : Fin (m n + 1) ↦ ν)).prod (dirichletOne (m n)))
    μ ν hA hB hσ hdist hμA hνB aplus aminus hplus hminus
    (fun _ w ↦ w.1) (fun _ j ↦ (measurable_pi_apply j).comp measurable_fst) hYlaw
    (fun _ w ↦ w.2) hfeasplus hfeasminus H hH E hE coord hcoord hu
    (fun n ↦ scale n ^ 2) (fun n ↦ sq_pos_of_pos (hscale n)) hscale2 scale D hD
    Energy hEnergy henergyplus henergyminus Q φ hφ hinner R ψ houter

end OTSelector.Reconstruction

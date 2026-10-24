import OTSelector.Reconstruction.FinslerPhysicalSceneRootedLocalCycleOriginal
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutLegality
import OTSelector.Transport.CyclicMonotonicity.CountableRectangleSupport

/-!
# Eventually absent actual rectangle witnesses survive iterated weak limits

Open-window masses are lower semicontinuous. Eventual zero witnesses from the
original physical-cost certificates therefore persist first in the sample-size
limit and then in the tilt limit. The two indices and their subsequences remain
separate; no homogeneous model cost is introduced.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Weak
variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

/-- An eventually absent nonnegative lower semicontinuous witness remains
absent in a weak limit. -/
theorem ae_eq_zero_of_weak_eventually_zero
    (P : ProbabilityMeasure S) (Pn : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto Pn atTop (𝓝 P)) (W : S → ℝ≥0∞)
    (hW : LowerSemicontinuous W)
    (hzero : ∀ᶠ n in atTop, ∀ᵐ s ∂(Pn n : Measure S), W s = 0) :
    ∀ᵐ s ∂(P : Measure S), W s = 0 := by
  apply ae_eq_zero_of_lowerSemicontinuous_lintegral_tendsto_zero P Pn hweak W hW
  apply tendsto_const_nhds.congr'
  filter_upwards [hzero] with n hn
  symm
  exact (lintegral_congr_ae hn).trans lintegral_zero

/-- Eventual sample-size certificates pass through an inner limit at each
sufficiently small tilt, and then through the independent outer tilt limit. -/
theorem ae_eq_zero_of_iterated_weak_eventually_zero
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, StrictMono (φ k))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hinner : ∀ k, Tendsto (fun N ↦ Pn k (φ k N)) atTop (𝓝 (Q k)))
    (houter : Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R))
    (W : S → ℝ≥0∞) (hW : LowerSemicontinuous W)
    (hzero : ∀ᶠ k in atTop, ∀ᶠ N in atTop,
      ∀ᵐ s ∂(Pn k N : Measure S), W s = 0) :
    ∀ᵐ s ∂(R : Measure S), W s = 0 := by
  have hQ : ∀ᶠ k in atTop, ∀ᵐ s ∂(Q k : Measure S), W s = 0 := by
    filter_upwards [hzero] with k hk
    exact ae_eq_zero_of_weak_eventually_zero (Q k) (fun N ↦ Pn k (φ k N))
      (hinner k) W hW ((hφ k).tendsto_atTop.eventually hk)
  exact ae_eq_zero_of_weak_eventually_zero R (fun k ↦ Q (ψ k)) houter W hW
    (hψ.tendsto_atTop.eventually hQ)

end Weak

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]

local instance actualRootedCycleLimitPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The actual two open-window mass witness in either component of the scene. -/
def physicalSceneRectangleWitness (plus : Bool)
    (U V : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    (s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) : ℝ≥0∞ :=
  min (((if plus then s.1 else s.2) : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) U)
      (((if plus then s.1 else s.2) : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) V)

/-- Only openness of the two observed windows is needed for the weak-limit
witness. The physical cost certificate is kept outside this topological step. -/
theorem lowerSemicontinuous_physicalSceneRectangleWitness
    (plus : Bool) {U V : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))}
    (hU : IsOpen U) (hV : IsOpen V) :
    LowerSemicontinuous (physicalSceneRectangleWitness plus U V) := by
  cases plus
  · change LowerSemicontinuous (fun s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
      min ((s.2 : Measure _) U) ((s.2 : Measure _) V))
    exact ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hU).comp continuous_snd).inf
      ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hV).comp continuous_snd)
  · change LowerSemicontinuous (fun s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
      min ((s.1 : Measure _) U) ((s.1 : Measure _) V))
    exact ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hU).comp continuous_fst).inf
      ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hV).comp continuous_fst)

/-- The original environment/root certificates give the zero-window witness
under the SAME actual pair scene law, with all restricted columns unchanged. -/
theorem ae_actualAllocationRootedSceneLaw_rectangle_witness_zero
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure M) [IsFiniteMeasure μ]
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (hap : ∀ j, Measurable (fun z : Ω × M ↦ ap z.1 z.2 j))
    (ham : ∀ j, Measurable (fun z : Ω × M ↦ am z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    (plus : Bool) (U V : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    (hU : IsOpen U) (hV : IsOpen V)
    (hzero : ∀ᵐ w ∂P, ∀ z : ι → ℝ,
      min
        (physicalSceneRootedPlan
          ((physicalSceneGlobalAllocationFamily μ (if plus then ap else am) Y w).restrict
            (H ×ˢ univ)) coord u N z U)
        (physicalSceneRootedPlan
          ((physicalSceneGlobalAllocationFamily μ (if plus then ap else am) Y w).restrict
            (H ×ˢ univ)) coord u N z V) = 0) :
    ∀ᵐ s ∂(actualAllocationRootedSceneLaw P μ ap am hap ham Y hY H hH coord hcoord
      u hu N hN D hD : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
      physicalSceneRectangleWitness plus U V s = 0 := by
  let Γp := fun w ↦ (physicalSceneGlobalAllocationFamily μ ap Y w).restrict (H ×ˢ univ)
  let Γm := fun w ↦ (physicalSceneGlobalAllocationFamily μ am Y w).restrict (H ×ˢ univ)
  let observation := physicalSceneRootedLocalScene Γp Γm coord u N
  have hp := measurable_physicalPlan_sourceRestriction (physicalSceneGlobalAllocationFamily μ ap Y)
    (measurable_physicalSceneGlobalAllocationFamily μ ap hap Y hY) H hH
  have hm := measurable_physicalPlan_sourceRestriction (physicalSceneGlobalAllocationFamily μ am Y)
    (measurable_physicalSceneGlobalAllocationFamily μ am ham Y hY) H hH
  have hobs := measurable_physicalSceneRootedLocalScene Γp Γm hp hm coord hcoord u hu N
  have hevent : MeasurableSet {s | physicalSceneRectangleWitness plus U V s = 0} :=
    measurableSet_eq_fun (lowerSemicontinuous_physicalSceneRectangleWitness plus hU hV).measurable
      measurable_const
  have : IsProbabilityMeasure (cavityRootMeasure volume D N) :=
    isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  have hz : ∀ᵐ v : Ω × (ι → ℝ) ∂P.prod (cavityRootMeasure volume D N),
      ∀ z : ι → ℝ, min
        (physicalSceneRootedPlan
          ((physicalSceneGlobalAllocationFamily μ (if plus then ap else am) Y v.1).restrict
            (H ×ˢ univ)) coord u N z U)
        (physicalSceneRootedPlan
          ((physicalSceneGlobalAllocationFamily μ (if plus then ap else am) Y v.1).restrict
            (H ×ˢ univ)) coord u N z V) = 0 :=
    measurePreserving_fst.quasiMeasurePreserving.ae hzero
  change ∀ᵐ s ∂(P.prod (cavityRootMeasure volume D N)).map observation,
    physicalSceneRectangleWitness plus U V s = 0
  apply (ae_map_iff hobs.aemeasurable hevent).mpr
  filter_upwards [hz] with v hv
  cases plus <;> simpa [physicalSceneRectangleWitness, physicalSceneRootedLocalScene,
    physicalSceneRootedLocalPlan, Γp, Γm] using hv v.2

/-- Actual zero rectangle witnesses pass through the inner sample-size and
outer tilt limits without choosing a diagonal sequence. -/
theorem ae_physicalSceneRectangleWitness_zero_of_iterated_weak
    (Pn : ℕ → ℕ → ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (Q : ℕ → ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (R : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, StrictMono (φ k)) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hinner : ∀ k, Tendsto (fun N ↦ Pn k (φ k N)) atTop (𝓝 (Q k)))
    (houter : Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R))
    (plus : Bool) {U V : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))}
    (hU : IsOpen U) (hV : IsOpen V)
    (hzero : ∀ᶠ k in atTop, ∀ᶠ N in atTop,
      ∀ᵐ s ∂(Pn k N : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
        physicalSceneRectangleWitness plus U V s = 0) :
    ∀ᵐ s ∂(R : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
      physicalSceneRectangleWitness plus U V s = 0 :=
  ae_eq_zero_of_iterated_weak_eventually_zero Pn Q R φ hφ ψ hψ hinner houter
    (physicalSceneRectangleWitness plus U V)
    (lowerSemicontinuous_physicalSceneRectangleWitness plus hU hV) hzero

end OTSelector.Reconstruction

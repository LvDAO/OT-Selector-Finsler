import OTSelector.Probability.CavitySemidiscreteRootedEnergy
import OTSelector.Reconstruction.OriginalIIDFullSeedLocalCountMoments
import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalPlan
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootScale
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Averaged original endpoint escape from a fixed compact macroscopic core.
Only the shrinking exterior collar is charged; no boundary-null hypothesis or
pointwise growing-count majorant is required. -/
open Set Function Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

/-- The literal original coordinate endpoint lies outside K, but inside the
same bounded rooted spatial window over c. -/
def rootCoreEscapeSet {q : ℕ} (K : Set (Fin q → ℝ)) (R scale : ℝ)
    (c : Fin q → ℝ) : Set (Fin q → ℝ) :=
  Kᶜ ∩ (fun x ↦ scale • (x-c)) ⁻¹' closedBall 0 R

theorem measurableSet_rootCoreEscapeSet {q : ℕ} {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (R scale : ℝ) (c : Fin q → ℝ) :
    MeasurableSet (rootCoreEscapeSet K R scale c) :=
  hK.compl.inter (measurableSet_closedBall.preimage (by fun_prop))

/-- The true q-dimensional Haar Jacobian cancels the original mass factor. -/
theorem volume_scaled_window_cancel {q : ℕ} (scale : ℝ) (hs : 0 < scale) (R : ℝ) :
    ENNReal.ofReal (scale ^ q) *
      (volume : Measure (Fin q → ℝ)) ((fun x ↦ scale • x) ⁻¹' closedBall 0 R) =
        (volume : Measure (Fin q → ℝ)) (closedBall 0 R) := by
  have hmap := Measure.map_addHaar_smul (volume : Measure (Fin q → ℝ)) hs.ne'
  have h := congrArg (fun m : Measure (Fin q → ℝ) ↦ m (closedBall 0 R)) hmap
  rw [Measure.map_apply (by fun_prop) measurableSet_closedBall,Measure.smul_apply] at h
  have hsp : 0 < scale ^ q := pow_pos hs q
  have hi : ENNReal.ofReal |(scale ^ q)⁻¹| = (ENNReal.ofReal (scale ^ q))⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr hsp),ENNReal.ofReal_inv_of_pos hsp]
  simp only [Module.finrank_fin_fun,smul_eq_mul] at h
  rw [hi] at h
  rw [h,← mul_assoc,ENNReal.mul_inv_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr hsp)) ENNReal.ofReal_ne_top,one_mul]

/-- Averaging over the SAME compact macro core controls all exterior endpoint
mass by the true shrinking exterior collar. The factor scale^q cancels exactly. -/
theorem lintegral_rootCoreEscape_le {q : ℕ}
    (τ : Measure (Fin q → ℝ)) [IsFiniteMeasure τ]
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (R scale : ℝ) (hs : 0 < scale) :
    (∫⁻ c in K, ENNReal.ofReal (scale ^ q) * τ (rootCoreEscapeSet K R scale c) ∂volume) ≤
      (volume : Measure (Fin q → ℝ)) (closedBall 0 R) *
        τ (cthickening (R / scale) K \ K) := by
  let B : Set (Fin q → ℝ) := (fun x ↦ scale • x) ⁻¹' closedBall 0 R
  let collar := cthickening (R / scale) K \ K
  have hB : MeasurableSet B := measurableSet_closedBall.preimage (by fun_prop)
  have hcollar : MeasurableSet collar := isClosed_cthickening.measurableSet.diff hK.measurableSet
  have hpoint (c : Fin q → ℝ) (hc : c ∈ K) :
      τ (rootCoreEscapeSet K R scale c) ≤
        cavityRootWindowReadout (τ.restrict collar) id (fun _ ↦ 1) B c := by
    let W : Set (Fin q → ℝ) := {x | x-c ∈ B}
    have hW : MeasurableSet W := hB.preimage (by fun_prop)
    change τ (rootCoreEscapeSet K R scale c) ≤
      ∫⁻ x, W.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂τ.restrict collar
    rw [lintegral_indicator_fun_one hW,Measure.restrict_apply hW]
    apply measure_mono
    intro x hx
    refine ⟨hx.2,?_,hx.1⟩
    apply mem_cthickening_of_dist_le x c (R/scale) K hc
    have hn : ‖scale • (x-c)‖ ≤ R := by
      have hxball : scale • (x-c) ∈ closedBall (0 : Fin q → ℝ) R := hx.2
      simpa only [mem_closedBall,dist_zero_right] using hxball
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs] at hn
    rw [dist_eq_norm]
    exact (le_div_iff₀ hs).mpr (by nlinarith)
  have hmass : (τ.restrict collar) univ = τ collar := by simp
  calc
    _ ≤ ∫⁻ c in K, ENNReal.ofReal (scale ^ q) *
        cavityRootWindowReadout (τ.restrict collar) id (fun _ ↦ 1) B c ∂volume := by
      apply setLIntegral_mono' hK.measurableSet
      intro c hc
      exact mul_le_mul_of_nonneg_left (hpoint c hc) bot_le
    _ ≤ ∫⁻ c, ENNReal.ofReal (scale ^ q) *
        cavityRootWindowReadout (τ.restrict collar) id (fun _ ↦ 1) B c ∂volume :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal (scale ^ q) * ((volume : Measure (Fin q → ℝ)) B * τ collar) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_cavityRootWindowReadout volume (τ.restrict collar) id measurable_id
          (fun _ ↦ 1) measurable_const B hB]
      simp
    _ = _ := by
      rw [← mul_assoc,volume_scaled_window_cancel scale hs R]

/-- Exterior collars of a fixed closed core have vanishing original finite
measure, even when its boundary has positive measure. -/
theorem tendsto_measure_exterior_cthickening {q : ℕ}
    (τ : Measure (Fin q → ℝ)) [IsFiniteMeasure τ]
    {K : Set (Fin q → ℝ)} (hK : IsClosed K) :
    Tendsto (fun radius : ℝ ↦ τ (cthickening radius K \ K)) (𝓝 0) (𝓝 0) := by
  have h := tendsto_measure_cthickening_of_isClosed
    (μ := τ.restrict Kᶜ) (s := K) ⟨1,zero_lt_one,measure_ne_top _ _⟩ hK
  simpa only [Measure.restrict_apply isClosed_cthickening.measurableSet,
    Measure.restrict_apply hK.measurableSet,inter_compl_self,measure_empty,Set.sdiff_eq] using h

/-- The actual scaled local exterior count vanishes after averaging over the
same compact macro core. Both source and target finite coordinate laws qualify. -/
theorem tendsto_lintegral_rootCoreEscape {q : ℕ}
    (τ : Measure (Fin q → ℝ)) [IsFiniteMeasure τ]
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (R : ℝ)
    (scale : ℕ → ℝ) (hs : ∀ n, 0 < scale n) (hlarge : Tendsto scale atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ c in K, ENNReal.ofReal (scale n ^ q) *
      τ (rootCoreEscapeSet K R (scale n) c) ∂volume) atTop (𝓝 0) := by
  have hr : Tendsto (fun n ↦ R / scale n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlarge
  have ht := (tendsto_measure_exterior_cthickening τ hK.isClosed).comp hr
  have hfin : (volume : Measure (Fin q → ℝ)) (closedBall 0 R) ≠ ∞ :=
    (isCompact_closedBall (0 : Fin q → ℝ) R).measure_lt_top.ne
  have hu := ENNReal.Tendsto.const_mul ht (Or.inr hfin)
  simp only [mul_zero] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ ↦ bot_le) (fun n ↦ lintegral_rootCoreEscape_le τ hK R (scale n) (hs n))


/-- The literal unchanged iid endpoint count outside the same compact core
vanishes after macro averaging. The original source mask H is retained before
coordinate pushforward; no conditioning or replacement of observations occurs. -/
theorem tendsto_lintegral_iid_rootCoreEscapeCount
    {Ω : Type*} [MeasurableSpace Ω] {q : ℕ}
    (η : Measure Ω) [IsProbabilityMeasure η]
    {H : Set Ω} (hH : MeasurableSet H) (coord : Ω → Fin q → ℝ) (hcoord : Measurable coord)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (R : ℝ)
    (scale : ℕ → ℝ) (hs : ∀ n, 0 < scale n) (hlarge : Tendsto scale atTop atTop)
    (hnormalization : ∀ n, scale n ^ q = ((n+1 : ℕ) : ℝ)) :
    Tendsto (fun n ↦ ∫⁻ c in K,
      ∫⁻ sample : Fin (n+1) → Ω, ∑ i : Fin (n+1),
        (H ∩ coord ⁻¹' rootCoreEscapeSet K R (scale n) c).indicator
          (fun _ ↦ (1 : ℝ≥0∞)) (sample i)
        ∂Measure.pi (fun _ : Fin (n+1) ↦ η) ∂volume) atTop (𝓝 0) := by
  let τ : Measure (Fin q → ℝ) := (η.restrict H).map coord
  have heq (n : ℕ) (c : Fin q → ℝ) :
      (∫⁻ sample : Fin (n+1) → Ω, ∑ i : Fin (n+1),
        (H ∩ coord ⁻¹' rootCoreEscapeSet K R (scale n) c).indicator
          (fun _ ↦ (1 : ℝ≥0∞)) (sample i)
        ∂Measure.pi (fun _ : Fin (n+1) ↦ η)) =
      ENNReal.ofReal (scale n ^ q) * τ (rootCoreEscapeSet K R (scale n) c) := by
    have hA := measurableSet_rootCoreEscapeSet hK.measurableSet R (scale n) c
    rw [OTSelector.Reconstruction.lintegral_iid_indicatorCount_eq η
      (hH.inter (hA.preimage hcoord)) (n+1)]
    have hτ : τ (rootCoreEscapeSet K R (scale n) c) =
        η (H ∩ coord ⁻¹' rootCoreEscapeSet K R (scale n) c) := by
      change ((η.restrict H).map coord) _ = _
      rw [Measure.map_apply hcoord hA,Measure.restrict_apply (hA.preimage hcoord),inter_comm]
    have hN : ENNReal.ofReal (scale n ^ q) = ((n+1 : ℕ) : ℝ≥0∞) := by
      rw [hnormalization n]
      exact ENNReal.ofReal_natCast (n+1)
    rw [hτ,hN]
  simp_rw [heq]
  exact tendsto_lintegral_rootCoreEscape τ hK R scale hs hlarge

/-- The canonical growing iid scale has precisely N=n+1 original observations.
The averaged core escape conclusion has no scaling-normalization callback. -/
theorem tendsto_lintegral_iid_canonical_rootCoreEscapeCount
    {Ω : Type*} [MeasurableSpace Ω] {q : ℕ} (hq : 0 < q)
    (η : Measure Ω) [IsProbabilityMeasure η]
    {H : Set Ω} (hH : MeasurableSet H) (coord : Ω → Fin q → ℝ) (hcoord : Measurable coord)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (R : ℝ) :
    Tendsto (fun n ↦ ∫⁻ c in K,
      ∫⁻ sample : Fin (n+1) → Ω, ∑ i : Fin (n+1),
        (H ∩ coord ⁻¹' rootCoreEscapeSet K R
          (2 * OTSelector.Reconstruction.haarRootRadius q ((n+1 : ℕ) : ℝ)) c).indicator
          (fun _ ↦ (1 : ℝ≥0∞)) (sample i)
        ∂Measure.pi (fun _ : Fin (n+1) ↦ η) ∂volume) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ ↦ ((n+1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  apply tendsto_lintegral_iid_rootCoreEscapeCount η hH coord hcoord hK R
    (fun n ↦ 2 * OTSelector.Reconstruction.haarRootRadius q ((n+1 : ℕ) : ℝ))
  · intro n
    exact mul_pos (by norm_num) (OTSelector.Reconstruction.haarRootRadius_pos q (by positivity))
  · exact (OTSelector.Reconstruction.tendsto_haarRootRadius q hq hN).const_mul_atTop (by norm_num)
  · intro n
    exact OTSelector.Reconstruction.haarRootRadius_mass q hq (by positivity)

end OTSelector.Probability

namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Any further source restriction of the SAME actual optimizer has no more
source endpoint mass than the literal original source array count. -/
theorem originalIIDOptimalPhysicalPlan_restrict_source_mass_le_count
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} [NeZero n] (cost : X → Y → ℝ) (energyScale : ℝ)
    (ξ : (Fin n → X) × (Fin n → Y)) (H : Set X)
    {A : Set X} (hA : MeasurableSet A) :
    (n : ℝ≥0∞) * ((originalIIDOptimalPhysicalPlan cost energyScale ξ).restrict (H ×ˢ univ))
      (Prod.fst ⁻¹' A) ≤ ∑ i : Fin n, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) (ξ.1 i) := by
  have hle : ((originalIIDOptimalPhysicalPlan cost energyScale ξ).restrict (H ×ˢ univ))
      (Prod.fst ⁻¹' A) ≤ empiricalMeasure ξ.1 A := by
    calc
      _ ≤ (originalIIDOptimalPhysicalPlan cost energyScale ξ) (Prod.fst ⁻¹' A) :=
        Measure.restrict_le_self _
      _ = _ := by
        rw [← Measure.map_apply measurable_fst hA,originalIIDOptimalPhysicalPlan_source]
  have hm : empiricalMeasure ξ.1 A = (n : ℝ≥0∞)⁻¹ *
      ∑ i : Fin n, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) (ξ.1 i) := by
    rw [← lintegral_indicator_fun_one hA,lintegral_originalEmpiricalMeasure _
      (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) (measurable_const.indicator hA)]
  calc
    _ ≤ (n : ℝ≥0∞) * empiricalMeasure ξ.1 A := mul_le_mul_of_nonneg_left hle bot_le
    _ = _ := by rw [hm,← mul_assoc,ENNReal.mul_inv_cancel
      (Nat.cast_ne_zero.mpr (NeZero.ne n)) (ENNReal.natCast_ne_top n),one_mul]

/-- Target endpoint loss of the SAME source-restricted optimizer is bounded by
the literal full original target array, without treating discarded edges as iid. -/
theorem originalIIDOptimalPhysicalPlan_restrict_target_mass_le_count
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} [NeZero n] (cost : X → Y → ℝ) (energyScale : ℝ)
    (ξ : (Fin n → X) × (Fin n → Y)) (H : Set X)
    {A : Set Y} (hA : MeasurableSet A) :
    (n : ℝ≥0∞) * ((originalIIDOptimalPhysicalPlan cost energyScale ξ).restrict (H ×ˢ univ))
      (Prod.snd ⁻¹' A) ≤ ∑ i : Fin n, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) (ξ.2 i) := by
  have hle : ((originalIIDOptimalPhysicalPlan cost energyScale ξ).restrict (H ×ˢ univ))
      (Prod.snd ⁻¹' A) ≤ empiricalMeasure ξ.2 A := by
    calc
      _ ≤ (originalIIDOptimalPhysicalPlan cost energyScale ξ) (Prod.snd ⁻¹' A) :=
        Measure.restrict_le_self _
      _ = _ := by
        rw [← Measure.map_apply measurable_snd hA,originalIIDOptimalPhysicalPlan_target]
  have hm : empiricalMeasure ξ.2 A = (n : ℝ≥0∞)⁻¹ *
      ∑ i : Fin n, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) (ξ.2 i) := by
    rw [← lintegral_indicator_fun_one hA,lintegral_originalEmpiricalMeasure _
      (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) (measurable_const.indicator hA)]
  calc
    _ ≤ (n : ℝ≥0∞) * empiricalMeasure ξ.2 A := mul_le_mul_of_nonneg_left hle bot_le
    _ = _ := by rw [hm,← mul_assoc,ENNReal.mul_inv_cancel
      (Nat.cast_ne_zero.mpr (NeZero.ne n)) (ENNReal.natCast_ne_top n),one_mul]


/-- The actual source-restricted original optimizer, tested for an endpoint
which remains in the same physical seed but escapes its coordinate core. -/
def originalIIDMaskedCoreEscapeMass
    {M : Type*} [MeasurableSpace M] {n q : ℕ}
    (cost : M → M → ℝ) (energyScale : ℝ) (H : Set M)
    (coord : M → Fin q → ℝ) (K : Set (Fin q → ℝ)) (R spatialScale : ℝ)
    (color : Fin 2) (c : Fin q → ℝ)
    (ξ : (Fin (n+1) → M) × (Fin (n+1) → M)) : ℝ≥0∞ :=
  ((n+1 : ℕ) : ℝ≥0∞) *
    ((originalIIDOptimalPhysicalPlan cost energyScale ξ).restrict (H ×ˢ univ))
      ((if color = 0 then Prod.fst else Prod.snd) ⁻¹'
        (H ∩ coord ⁻¹' rootCoreEscapeSet K R spatialScale c))

/-- For both original colors, the SAME optimized source-restricted plan loses
vanishing averaged endpoint mass through this coordinate-core guard. The proof
uses the unchanged full arrays, not a supposed iid law of unmatched leftovers. -/
theorem tendsto_lintegral_originalIIDMaskedCoreEscapeMass
    {M : Type*} [MeasurableSpace M] {q : ℕ}
    (η₀ η₁ : Measure M) [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
    {H : Set M} (hH : MeasurableSet H) (coord : M → Fin q → ℝ) (hcoord : Measurable coord)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (R : ℝ)
    (spatialScale : ℕ → ℝ) (hs : ∀ n, 0 < spatialScale n)
    (hlarge : Tendsto spatialScale atTop atTop)
    (hnormalization : ∀ n, spatialScale n ^ q = ((n+1 : ℕ) : ℝ))
    (cost : ℕ → M → M → ℝ) (energyScale : ℕ → ℝ) (color : Fin 2) :
    Tendsto (fun n ↦ ∫⁻ c in K,
      ∫⁻ ξ : (Fin (n+1) → M) × (Fin (n+1) → M),
        originalIIDMaskedCoreEscapeMass (cost n) (energyScale n) H coord K R
          (spatialScale n) color c ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ η₀)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ η₁)) ∂volume) atTop (𝓝 0) := by
  let η := if color = 0 then η₀ else η₁
  letI : IsProbabilityMeasure η := by dsimp [η]; split_ifs <;> infer_instance
  let A := fun n c ↦ H ∩ coord ⁻¹' rootCoreEscapeSet K R (spatialScale n) c
  have hA (n : ℕ) (c : Fin q → ℝ) : MeasurableSet (A n c) :=
    hH.inter ((measurableSet_rootCoreEscapeSet hK.measurableSet R (spatialScale n) c).preimage hcoord)
  let count := fun (n : ℕ) c (ξ : (Fin (n+1) → M) × (Fin (n+1) → M)) ↦
    ∑ i : Fin (n+1), (A n c).indicator (fun _ ↦ (1 : ℝ≥0∞))
      ((if color = 0 then ξ.1 else ξ.2) i)
  have hpoint (n : ℕ) (c : Fin q → ℝ)
      (ξ : (Fin (n+1) → M) × (Fin (n+1) → M)) :
      originalIIDMaskedCoreEscapeMass (cost n) (energyScale n) H coord K R
        (spatialScale n) color c ξ ≤ count n c ξ := by
    by_cases hc : color = 0
    · simpa only [originalIIDMaskedCoreEscapeMass,count,A,ite_eq_left hc] using
        originalIIDOptimalPhysicalPlan_restrict_source_mass_le_count
          (cost n) (energyScale n) ξ H (hA n c)
    · simpa only [originalIIDMaskedCoreEscapeMass,count,A,ite_eq_right hc] using
        originalIIDOptimalPhysicalPlan_restrict_target_mass_le_count
          (cost n) (energyScale n) ξ H (hA n c)
  have hcount (n : ℕ) (c : Fin q → ℝ) :
      (∫⁻ ξ : (Fin (n+1) → M) × (Fin (n+1) → M), count n c ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ η₀)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ η₁))) =
      (∫⁻ sample : Fin (n+1) → M, ∑ i : Fin (n+1),
        (A n c).indicator (fun _ ↦ (1 : ℝ≥0∞)) (sample i)
        ∂Measure.pi (fun _ : Fin (n+1) ↦ η)) := by
    let array : ((Fin (n+1) → M) × (Fin (n+1) → M)) → (Fin (n+1) → M) :=
      if color = 0 then Prod.fst else Prod.snd
    have hmarray : Measurable array := by
      dsimp [array]; split_ifs <;> fun_prop
    have hmap : ((Measure.pi (fun _ : Fin (n+1) ↦ η₀)).prod
        (Measure.pi (fun _ : Fin (n+1) ↦ η₁))).map array =
        Measure.pi (fun _ : Fin (n+1) ↦ η) := by
      dsimp [array,η]
      split_ifs
      · rw [Measure.map_fst_prod]; simp
      · rw [Measure.map_snd_prod]; simp
    have hm : Measurable (fun sample : Fin (n+1) → M ↦ ∑ i : Fin (n+1),
        (A n c).indicator (fun _ ↦ (1 : ℝ≥0∞)) (sample i)) :=
      Finset.measurable_sum _ (fun i _ ↦
        (measurable_const.indicator (hA n c)).comp (measurable_pi_apply i))
    have heq : count n c = (fun sample : Fin (n+1) → M ↦ ∑ i : Fin (n+1),
        (A n c).indicator (fun _ ↦ (1 : ℝ≥0∞)) (sample i)) ∘ array := by
      funext ξ
      dsimp [count,array]
      split_ifs <;> rfl
    rw [heq]
    simp only [Function.comp_def]
    rw [← lintegral_map hm hmarray,hmap]
  have hu := tendsto_lintegral_iid_rootCoreEscapeCount η hH coord hcoord hK R
    spatialScale hs hlarge hnormalization
  change Tendsto (fun n ↦ ∫⁻ c in K,
    ∫⁻ sample : Fin (n+1) → M, ∑ i : Fin (n+1),
      (A n c).indicator (fun _ ↦ (1 : ℝ≥0∞)) (sample i)
      ∂Measure.pi (fun _ : Fin (n+1) ↦ η) ∂volume) atTop (𝓝 0) at hu
  simp_rw [← hcount] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ ↦ bot_le) (fun n ↦ lintegral_mono fun c ↦ lintegral_mono (hpoint n c))


/-- The same two-product optimized experiment at the actual canonical spatial
scale, with the integer endpoint prefactor exactly N=n+1. -/
theorem tendsto_lintegral_originalIID_canonical_maskedCoreEscapeMass
    {M : Type*} [MeasurableSpace M] {q : ℕ} (hq : 0 < q)
    (η₀ η₁ : Measure M) [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
    {H : Set M} (hH : MeasurableSet H) (coord : M → Fin q → ℝ) (hcoord : Measurable coord)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (R : ℝ)
    (cost : ℕ → M → M → ℝ) (energyScale : ℕ → ℝ) (color : Fin 2) :
    Tendsto (fun n ↦ ∫⁻ c in K,
      ∫⁻ ξ : (Fin (n+1) → M) × (Fin (n+1) → M),
        originalIIDMaskedCoreEscapeMass (cost n) (energyScale n) H coord K R
          (2 * haarRootRadius q ((n+1 : ℕ) : ℝ)) color c ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ η₀)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ η₁)) ∂volume) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ ↦ ((n+1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  apply tendsto_lintegral_originalIIDMaskedCoreEscapeMass η₀ η₁ hH coord hcoord hK R
    (fun n ↦ 2 * haarRootRadius q ((n+1 : ℕ) : ℝ))
    (fun n ↦ mul_pos (by norm_num) (haarRootRadius_pos q (by positivity)))
    ((tendsto_haarRootRadius q hq hN).const_mul_atTop (by norm_num))
    (fun n ↦ haarRootRadius_mass q hq (by positivity)) cost energyScale color

section OriginalGeometry
open Manifold Module OTSelector.Geometry
open scoped ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
namespace PopulationLocalPressureCore

omit [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] in
/-- Inside the SAME fixed original seed, escaping the original root core is
exactly escaping its original coordinate image. This is literal set equality. -/
theorem original_core_escape_mask_eq_coordinate
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) :
    let C := D.haar.continuous.coefficient i
    let w := populationSeedRootLabelValue (P C.seedIndex).seed a
    let e := (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
    H \ a ⁻¹' C.roots = H ∩ (fun x ↦ e (w (a x))) ⁻¹' (e '' (w '' C.roots))ᶜ := by
  intro C w e H
  rw [D.original_core_mask_eq_full_seed_inter_coordinate hF hcomplete hu ha hinj i]
  ext x
  change (x ∈ H ∧ ¬ (x ∈ H ∧ e (w (a x)) ∈ e '' (w '' C.roots))) ↔
    (x ∈ H ∧ e (w (a x)) ∉ e '' (w '' C.roots))
  tauto

/-- Original geometric data supply the actual fixed seed, actual compact
coordinate core and actual iid optimizer on both colors. Its canonical averaged
original-label core escape tends to zero, without an energy or tail premise. -/
theorem original_iid_canonical_core_escape_tendsto
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count)
    (hq : 0 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (R : ℝ) (cost : ℕ → M → M → ℝ) (energyScale : ℕ → ℝ) (color : Fin 2) :
    let C := D.haar.continuous.coefficient i
    let w := populationSeedRootLabelValue (P C.seedIndex).seed a
    let e := (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
    let K := e '' (w '' C.roots)
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
    Tendsto (fun n ↦ ∫⁻ c in K,
      ∫⁻ ξ : (Fin (n+1) → M) × (Fin (n+1) → M),
        originalIIDMaskedCoreEscapeMass (cost n) (energyScale n) H (fun x ↦ e (w (a x))) K R
          (2 * haarRootRadius (finrank ℝ (P C.seedIndex).seed.covector.ker)
            ((n+1 : ℕ) : ℝ)) color c ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ η₀)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ η₁)) ∂volume) atTop (𝓝 0) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  intro C w e K H
  have hw : ContinuousOn w C.roots := by
    simpa only [D.haar.intensity_roots i] using (D.haar.intensity i).continuous_label
  have hK : IsCompact K := (C.roots_compact.image_of_continuousOn hw).image e.continuous
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj C.seedIndex
  have hcoord : Measurable (fun x ↦ e (w (a x))) :=
    e.continuous.measurable.comp
      ((measurable_populationSeedRootLabelValue (P C.seedIndex).seed hF hcomplete hu ha hinj).comp ha)
  exact tendsto_lintegral_originalIID_canonical_maskedCoreEscapeMass hq η₀ η₁
    hH _ hcoord hK R cost energyScale color

end PopulationLocalPressureCore
end OriginalGeometry
end OTSelector.Reconstruction

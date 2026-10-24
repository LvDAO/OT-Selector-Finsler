import OTSelector.Reconstruction.MarkedStationaryValuePalmRootedEnergy
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootScale
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootPhysicalScene

/-!
# Actual original finite-plan sequences produce stationary pair Palm limits

Original mass bounds give tightness of the actual Haar-rooted laws. Their
subsequence and weak scene limit are chosen internally. The actual root-change
cocycle gives stationarity, while exact Haar energy bounds and source-window
cutoff removal produce the constructed q-dimensional Palm energy bound.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
local instance markedStationaryValuePalmRootedLimitLocalPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValuePalmRootedLimitLocalNonempty : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0, inferInstance⟩⟩

/-- The same original finite plans produce an actual stationary qdim scene and
its own finite paired-edge Palm, whose mass and continuous nonnegative energy
obey the original global bounds. No weak-limit or stationarity premise is used. -/
theorem exists_stationary_cubePalm_of_original_finitePlans
    (hq : 0 < Fintype.card ι)
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (Γ : ∀ k, Ω k → Measure (M × M)) [∀ k w, IsFiniteMeasure (Γ k w)]
    (hΓ : ∀ k, Measurable (Γ k))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ k, 0 < N k) (hlarge : Tendsto N atTop atTop)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmass : ∀ k, (∫⁻ w, Γ k w univ ∂P k) ≤ C)
    (f : PhysicalPairPalmMark ι → ℝ) (hf : Continuous f) (hf0 : ∀ m, 0 ≤ f m)
    (E : ℝ≥0∞)
    (henergy : ∀ k, (∫⁻ w, ∫⁻ p,
      ENNReal.ofReal (f ((u p.1, u p.2), coord k p.2 - coord k p.1)) ∂Γ k w ∂P k) ≤ E) :
    ∃ Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ physicalSceneRootedLocalSceneLaw (P (φ k)) (Γ (φ k)) (Γ (φ k))
        (hΓ (φ k)) (hΓ (φ k)) (coord (φ k)) (hcoord (φ k)) u hu (N (φ k)) (hN (φ k))
        (haarRootCube ι (haarRootRadius (Fintype.card ι) (N (φ k))))
        (volume_haarRootCube_radius ι hq (hN (φ k)))) atTop (𝓝 Q) ∧
      (∀ v : ι → ℝ, MeasurePreserving (physicalSceneReroot v)
        (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
        (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ∧
      cubePalm ι (physicalScenePairCampbell
        (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) univ ≤ C ∧
      (∫⁻ m, ENNReal.ofReal (f m) ∂cubePalm ι (physicalScenePairCampbell
        (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))))) ≤ E ∧
      physicalScenePairCampbell
        (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) =
        (volume : Measure (ι → ℝ)).prod (cubePalm ι (physicalScenePairCampbell
          (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))))) := by
  let R (k : ℕ) := haarRootRadius (Fintype.card ι) (N k)
  let D (k : ℕ) := haarRootCube ι (R k)
  have hR (k) : 0 < R k := haarRootRadius_pos _ (hN k)
  have hD (k) : volume (D k) = ENNReal.ofReal (N k) :=
    volume_haarRootCube_radius ι hq (hN k)
  obtain ⟨Q, φ, hφ, hw⟩ := exists_tendsto_subseq_physicalSceneRestrictedRootedLocalSceneLaw
    P Γ Γ hΓ hΓ (fun _ ↦ univ) (fun _ ↦ MeasurableSet.univ)
    coord hcoord u hu N hN D hD C hC hmass hmass
  have hweak : Tendsto (fun k ↦ physicalSceneRootedLocalSceneLaw (P (φ k)) (Γ (φ k)) (Γ (φ k))
      (hΓ (φ k)) (hΓ (φ k)) (coord (φ k)) (hcoord (φ k)) u hu (N (φ k)) (hN (φ k))
      (D (φ k)) (hD (φ k))) atTop (𝓝 Q) := by
    simpa only [physicalSceneRestrictedRootedLocalSceneLaw, univ_prod_univ, Measure.restrict_univ] using hw
  have hstat (v : ι → ℝ) : MeasurePreserving (physicalSceneReroot v)
      (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
      (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :=
    measurePreserving_physicalSceneReroot_of_cubeRooted_tendsto
      (fun k ↦ P (φ k)) (fun k ↦ Γ (φ k)) (fun k ↦ Γ (φ k))
      (fun k ↦ hΓ (φ k)) (fun k ↦ hΓ (φ k))
      (fun k ↦ coord (φ k)) (fun k ↦ hcoord (φ k)) u hu
      (fun k ↦ N (φ k)) (fun k ↦ R (φ k)) (fun k ↦ hN (φ k)) (fun k ↦ hR (φ k))
      (fun k ↦ hD (φ k)) ((tendsto_haarRootRadius _ hq hlarge).comp hφ.tendsto_atTop) hweak v
  have henergyLimit := lintegral_cubePalm_le_of_weak_energy_density_bound _ hweak f hf hf0 E
    (fun U hU k ↦ (lintegral_physicalSceneRootedLocalSceneLaw_sourceEnergy_le
      (P (φ k)) (Γ (φ k)) (Γ (φ k)) (hΓ (φ k)) (hΓ (φ k))
      (coord (φ k)) (hcoord (φ k)) u hu (N (φ k)) (hN (φ k)) (D (φ k)) (hD (φ k))
      (f := fun m ↦ ENNReal.ofReal (f m))
      (ENNReal.measurable_ofReal.comp hf.measurable) U hU.measurableSet).trans
        (mul_le_mul_of_nonneg_left (henergy (φ k)) bot_le))
  have hmassLimit := lintegral_cubePalm_le_of_weak_energy_density_bound _ hweak
    (fun _ ↦ (1 : ℝ)) continuous_const (fun _ ↦ zero_le_one) C ?_
  · have hm : cubePalm ι (physicalScenePairCampbell
        (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) univ ≤ C := by
      simpa only [ENNReal.ofReal_one, lintegral_const, one_mul, Measure.restrict_apply_univ] using hmassLimit
    have hunit : (∫⁻ scene,
        (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
          {e | e.1.1 ∈ palmUnitCube ι}
        ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) < ∞ := by
      have hb := hm.trans_lt (lt_top_iff_ne_top.mpr hC)
      rwa [cubePalm_apply ι _ MeasurableSet.univ, physicalScenePairCampbell_unitCube] at hb
    exact ⟨Q, φ, hφ, hweak, hstat, hm, henergyLimit,
      physicalScenePairCampbell_eq_volume_prod_cubePalm _ hstat hunit⟩
  · intro U hU k
    have h := lintegral_physicalSceneRootedLocalSceneLaw_sourceEnergy_le
      (P (φ k)) (Γ (φ k)) (Γ (φ k)) (hΓ (φ k)) (hΓ (φ k))
      (coord (φ k)) (hcoord (φ k)) u hu (N (φ k)) (hN (φ k)) (D (φ k)) (hD (φ k))
      (f := fun _ ↦ (1 : ℝ≥0∞)) measurable_const U hU.measurableSet
    have hm : (∫⁻ w, ∫⁻ _p, (1 : ℝ≥0∞) ∂Γ (φ k) w ∂P (φ k)) ≤ C := by
      simpa only [lintegral_const, one_mul] using hmass (φ k)
    simpa only [ENNReal.ofReal_one] using
      h.trans (mul_le_mul_of_nonneg_left hm bot_le)

end OTSelector.Reconstruction

import OTSelector.Reconstruction.MarkedStationaryValueLegalFocalEnergyCutoff
import OTSelector.Topology.CompactCutoffExhaustion
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Lower semicontinuity of the original focal energy on its actual interior carrier. -/
open Set Function MeasureTheory Filter Topology
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The true shifted weighted energy is lower semicontinuous along original
Palm probabilities carried by the same legal interior. Clock cutoffs retain
the whole displacement, including its possible infinite second moment. -/
theorem lintegral_original_focal_shifted_le_liminf_of_weak
    (q : ℕ) {O W : Set (ℝ × ℝ)} (hO : IsOpen O) (hWO : W ⊆ O)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix O) (hpos : ∀ w ∈ O, (matrix w).PosSemidef)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hactual : ∀ w ∈ W, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (Function.uncurry g) O)
    {G : ℝ} (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (ηs : ℕ → ProbabilityMeasure (PhysicalPairPalmMark (Fin q)))
    (η : ProbabilityMeasure (PhysicalPairPalmMark (Fin q)))
    (hweak : Tendsto ηs atTop (𝓝 η))
    (hcarriers : ∀ n, ∀ᵐ m ∂(ηs n : Measure (PhysicalPairPalmMark (Fin q))), m.1 ∈ W)
    (hcarrier : ∀ᵐ m ∂(η : Measure (PhysicalPairPalmMark (Fin q))), m.1 ∈ W) :
    (∫⁻ m, ENNReal.ofReal (kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G)
      ∂(η : Measure (PhysicalPairPalmMark (Fin q)))) ≤
      liminf (fun n ↦ ∫⁻ m,
        ENNReal.ofReal (kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G)
          ∂(ηs n : Measure (PhysicalPairPalmMark (Fin q)))) atTop := by
  let shift (m : PhysicalPairPalmMark (Fin q)) :=
    kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G
  obtain ⟨χ, hχ, hχO, hχevent⟩ := exists_compact_cutoffs_eventually_one_of_isOpen O hO
  choose H hHn hHeq hHle using fun k ↦
    exists_continuous_legal_clockCutoff_shifted_minorant q matrix hmatrix hpos hkn
      hactual hg hgb t (χ k) (hχ k) (hχO k)
  have hbound (k : ℕ) :
      (∫⁻ m, ENNReal.ofReal (H k m) ∂(η : Measure (PhysicalPairPalmMark (Fin q)))) ≤
        liminf (fun n ↦ ∫⁻ m, ENNReal.ofReal (shift m)
          ∂(ηs n : Measure (PhysicalPairPalmMark (Fin q)))) atTop := by
    apply (lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      (H k).continuous (hHn k) (fun U hU ↦
        ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hU)).trans
    exact liminf_le_liminf (Filter.Eventually.of_forall fun n ↦
      lintegral_mono_ae ((hcarriers n).mono fun m hm ↦
        ENNReal.ofReal_le_ofReal (hHle k m hm)))
      (by isBoundedDefault) (by isBoundedDefault)
  have hconv : ∀ᵐ m ∂(η : Measure (PhysicalPairPalmMark (Fin q))),
      Tendsto (fun k ↦ ENNReal.ofReal (H k m)) atTop (𝓝 (ENNReal.ofReal (shift m))) := by
    filter_upwards [hcarrier] with m hm
    apply tendsto_const_nhds.congr'
    filter_upwards [hχevent m.1 (hWO hm)] with k hk
    rw [hHeq k m hm, hk, one_mul]
  calc
    _ = ∫⁻ m, liminf (fun k ↦ ENNReal.ofReal (H k m)) atTop
        ∂(η : Measure (PhysicalPairPalmMark (Fin q))) :=
      lintegral_congr_ae (hconv.mono fun _ hm ↦ hm.liminf_eq.symm)
    _ ≤ liminf (fun k ↦ ∫⁻ m, ENNReal.ofReal (H k m)
        ∂(η : Measure (PhysicalPairPalmMark (Fin q)))) atTop :=
      lintegral_liminf_le (fun k ↦ (H k).continuous.measurable.ennreal_ofReal)
    _ ≤ _ := liminf_le_of_frequently_le (Filter.Eventually.of_forall hbound).frequently

end OTSelector.Reconstruction

import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicRootMarginal
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootScale
import OTSelector.Probability.HaarAffineCube

/-!
# Exact macroscopic Haar root law at the original finite sample scale

Inverse spatial scaling of a normalized expanding original Haar domain gives
its fixed macroscopic restriction law. For the actual centered mass-N cubes,
this is exactly the normalized centered unit cube at every sample size.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The fixed original macro-domain restriction is a probability law when its
actual Lebesgue mass is one. This concerns only the Haar root experiment. -/
def physicalSceneUnitMassHaarLaw {ι : Type*} [Fintype ι]
    (K : Set (ι → ℝ)) (hK : volume K = 1) : ProbabilityMeasure (ι → ℝ) :=
  ⟨volume.restrict K, ⟨by rw [Measure.restrict_apply_univ, hK]⟩⟩

/-- Scaling an actual normalized Haar root back to any fixed unit-mass macro
domain recovers its exact original volume restriction. -/
theorem physicalSceneMacroscopicRootLaw_eq_unitMassHaarLaw
    (q n : ℕ) (side : ℝ≥0) (hside : 0 < side)
    (K : Set (Fin q → ℝ)) (hK : MeasurableSet K) (hKmass : volume K = 1)
    (hD : volume (physicalSceneMacroscopicRoot (side : ℝ) ⁻¹' K) =
      ENNReal.ofReal ((n : ℝ) + 1)) :
    physicalSceneMacroscopicRootLaw n (side : ℝ)
      (physicalSceneMacroscopicRoot (side : ℝ) ⁻¹' K) hD =
      physicalSceneUnitMassHaarLaw K hKmass := by
  have hf := (continuous_physicalSceneMacroscopicRoot (ι := Fin q) (side : ℝ)).measurable
  have heq : physicalSceneMacroscopicRoot (side : ℝ) =
      (fun z : Fin q → ℝ ↦ (side : ℝ)⁻¹ • z) := by
    ext z i
    simp only [physicalSceneMacroscopicRoot, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    exact mul_comm _ _
  have hmap : (volume : Measure (Fin q → ℝ)).map (physicalSceneMacroscopicRoot (side : ℝ)) =
      ((side ^ q : ℝ≥0) : ℝ≥0∞) • (volume : Measure (Fin q → ℝ)) := by
    rw [heq]
    simpa only [ENNReal.smul_def] using map_volume_inverse_smul_cube q hside
  have hrestriction :
      (volume.restrict (physicalSceneMacroscopicRoot (side : ℝ) ⁻¹' K)).map
        (physicalSceneMacroscopicRoot (side : ℝ)) = ((side ^ q : ℝ≥0) : ℝ≥0∞) • volume.restrict K := by
    rw [← Measure.restrict_map hf hK, hmap, Measure.restrict_smul]
  have hmass : ENNReal.ofReal ((n : ℝ) + 1) = ((side ^ q : ℝ≥0) : ℝ≥0∞) := by
    have hm := congrArg (fun μ : Measure (Fin q → ℝ) ↦ μ univ) hrestriction
    rw [Measure.map_apply hf MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ, hD, Measure.smul_apply,
      Measure.restrict_apply_univ, hKmass, smul_eq_mul, mul_one] at hm
    exact hm
  apply Subtype.ext
  change ((ENNReal.ofReal ((n : ℝ) + 1))⁻¹ •
    volume.restrict (physicalSceneMacroscopicRoot (side : ℝ) ⁻¹' K)).map
      (physicalSceneMacroscopicRoot (side : ℝ)) = volume.restrict K
  rw [Measure.map_smul, hrestriction, smul_smul, ← hmass,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top,
    one_smul]

/-- The original centered expanding cube is exactly the inverse-image of the
fixed centered unit cube under the actual macroscopic root map. -/
theorem physicalSceneMacroscopicRoot_preimage_centered_unitCube
    {ι : Type*} [Fintype ι] {scale : ℝ} (hscale : 0 < scale) :
    physicalSceneMacroscopicRoot scale ⁻¹' haarRootCube ι (1 / 2) =
      haarRootCube ι (scale / 2) := by
  ext z
  change ((fun i ↦ z i / scale) ∈ Icc (fun _ ↦ -(1 / 2 : ℝ)) (fun _ ↦ (1 / 2 : ℝ))) ↔
    z ∈ Icc (fun _ ↦ -(scale / 2)) (fun _ ↦ scale / 2)
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · intro i
      have h := (le_div_iff₀ hscale).mp (hl i)
      linarith
    · intro i
      have h := (div_le_iff₀ hscale).mp (hu i)
      linarith
  · rintro ⟨hl, hu⟩
    constructor
    · intro i
      apply (le_div_iff₀ hscale).mpr
      linarith [hl i]
    · intro i
      apply (div_le_iff₀ hscale).mpr
      linarith [hu i]

/-- The actual centered unit cube has unit Lebesgue mass. -/
theorem physicalScene_centered_unitCube_mass (ι : Type*) [Fintype ι] :
    volume (haarRootCube ι (1 / 2)) = 1 := by
  rw [volume_haarRootCube ι (by norm_num)]
  norm_num

/-- Every actual mass-N root cube has this same original macro marginal. -/
theorem physicalSceneMacroscopicRootLaw_haarRootRadius
    (q : ℕ) (hq : 0 < q) (n : ℕ) :
    physicalSceneMacroscopicRootLaw n (((n : ℝ) + 1) ^ (1 / (q : ℝ)))
      (haarRootCube (Fin q) (haarRootRadius q ((n : ℝ) + 1)))
      (by
        simpa only [Fintype.card_fin] using
          (volume_haarRootCube_radius (Fin q)
            (by simpa only [Fintype.card_fin] using hq) (N := (n : ℝ) + 1) (by positivity))) =
      physicalSceneUnitMassHaarLaw (haarRootCube (Fin q) (1 / 2))
        (physicalScene_centered_unitCube_mass (Fin q)) := by
  let scale := ((n : ℝ) + 1) ^ (1 / (q : ℝ))
  have hs : 0 < scale := Real.rpow_pos_of_pos (by positivity) _
  let side : ℝ≥0 := ⟨scale, hs.le⟩
  have hside : 0 < side := hs
  have hD : volume (physicalSceneMacroscopicRoot (side : ℝ) ⁻¹'
      haarRootCube (Fin q) (1 / 2)) = ENNReal.ofReal ((n : ℝ) + 1) := by
    change volume (physicalSceneMacroscopicRoot scale ⁻¹' haarRootCube (Fin q) (1 / 2)) = _
    rw [physicalSceneMacroscopicRoot_preimage_centered_unitCube hs]
    simpa only [haarRootRadius, scale, Fintype.card_fin] using
      (volume_haarRootCube_radius (Fin q)
        (by simpa only [Fintype.card_fin] using hq) (N := (n : ℝ) + 1) (by positivity))
  have hh := physicalSceneMacroscopicRootLaw_eq_unitMassHaarLaw q n side hside
    (haarRootCube (Fin q) (1 / 2)) isClosed_Icc.measurableSet
    (physicalScene_centered_unitCube_mass (Fin q)) hD
  have hcoe : (side : ℝ) = scale := rfl
  simpa only [hcoe, physicalSceneMacroscopicRoot_preimage_centered_unitCube hs,
    haarRootRadius] using hh

end OTSelector.Reconstruction

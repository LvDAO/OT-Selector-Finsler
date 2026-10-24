import OTSelector.Reconstruction.OriginalLegalScreeningPressureDilationFinite
import OTSelector.Reconstruction.OriginalReserveOrientedWindowIntensity
import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineShape

/-! Expected pressure on literal original arrays, using the existing unclamped
legal finite value and the actual same-frame volume. -/
open Set Function MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
open OTSelector.Probability

/-- Physical dilation of the actual arrays preserves every original count, clock
and index. The existing true-displacement finite legal value scales exactly. -/
theorem unclampedBlockLegalTilted_one_dilation {q : ℕ}
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    {c : ℝ} (hc : c ≠ 0)
    (hhom : ∀ a b v, kin a b (c • v) = c^2 * kin a b v) (t : ℝ)
    (arrays : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
    unclampedBlockLegalTilted q id id 1 kin g t
      (mapBlockData (legalMarkedPointDilation q c hc) arrays.1)
      (mapBlockData (legalMarkedPointDilation q c hc) arrays.2) =
      c^2 * unclampedBlockLegalTilted q id id 1 kin g (t/c^2) arrays.1 arrays.2 := by
  simpa only [unclampedBlockLegalTilted, Real.one_rpow, one_mul, id_eq,
    legalMarkedPhysicalTiltedEdge, mapBlockData, Pi.sub_def] using
      originalFiniteLegalValue_dilation arrays.1.2 arrays.2.2 kin g hc hhom t

/-- The equality holds under the same actual joined law, with no independence
between events, selected points or complete original arrays. -/
theorem integral_unclampedBlockLegalTilted_one_dilation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {q : ℕ}
    (arrays : Ω → BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    {c : ℝ} (hc : c ≠ 0)
    (hhom : ∀ a b v, kin a b (c • v) = c^2 * kin a b v) (t : ℝ) :
    (∫ ω, unclampedBlockLegalTilted q id id 1 kin g t
      (mapBlockData (legalMarkedPointDilation q c hc) (arrays ω).1)
      (mapBlockData (legalMarkedPointDilation q c hc) (arrays ω).2) ∂P) =
      c^2 * ∫ ω, unclampedBlockLegalTilted q id id 1 kin g (t/c^2)
        (arrays ω).1 (arrays ω).2 ∂P := by
  simp_rw [unclampedBlockLegalTilted_one_dilation kin g hc hhom t]
  exact integral_const_mul _ _

/-- The same oriented cube has its actual positive spatial Jacobian. -/
theorem originalOrientedPhysicalCube_realVolume_dilation {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {c R : ℝ} (hc : 0 < c) (hR : 0 ≤ R) :
    volume.real (originalCenteredPhysicalCubeRegion b (2*(c*R))) =
      c^q * volume.real (originalCenteredPhysicalCubeRegion b (2*R)) := by
  simp only [measureReal_def,volume_originalOrientedTraffic_cube,
    volume_haarRootCube (Fin q) (mul_nonneg hc.le hR),
    volume_haarRootCube (Fin q) hR,Fintype.card_fin,
    ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg hc.le hR)) q),
    ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hR) q)]
  rw [show 2*(c*R) = c*(2*R) by ring,mul_pow]

/-- Actual volume-normalized pressure has the precise intensity-times-quadratic
factor on the same joined original-array experiment. -/
theorem normalized_integral_unclampedBlockLegalTilted_one_dilation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {q : ℕ}
    (arrays : Ω → BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {c R : ℝ} (hc : 0 < c) (hR : 0 ≤ R)
    (hhom : ∀ a b v, kin a b (c • v) = c^2 * kin a b v) (t : ℝ) :
    (∫ ω, unclampedBlockLegalTilted q id id 1 kin g t
      (mapBlockData (legalMarkedPointDilation q c hc.ne') (arrays ω).1)
      (mapBlockData (legalMarkedPointDilation q c hc.ne') (arrays ω).2) ∂P) /
      volume.real (originalCenteredPhysicalCubeRegion b (2*(c*R))) =
      ((c^q)⁻¹*c^2) *
        ((∫ ω, unclampedBlockLegalTilted q id id 1 kin g (t/c^2)
          (arrays ω).1 (arrays ω).2 ∂P) /
          volume.real (originalCenteredPhysicalCubeRegion b (2*R))) := by
  rw [integral_unclampedBlockLegalTilted_one_dilation P arrays kin g hc.ne' hhom t,
    originalOrientedPhysicalCube_realVolume_dilation b hc hR]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The reciprocal quadratic factor of the actual intensity dilation. -/
theorem legalIntensityDilation_inverse_square {q : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ((legalIntensityDilation q ρ)^2)⁻¹ = ρ^(2/(q:ℝ)) := by
  unfold legalIntensityDilation
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le, ← Real.rpow_neg hρ.le]
  congr 1
  ring

/-- The original main intensity after the common dilation determines exactly the
finite-value comparison's fractional prefactor and tilt. It is not an assumed law change. -/
theorem normalized_integral_unclampedBlockLegalTilted_intensity_dilation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {q : ℕ} (hq : 0 < q)
    (arrays : Ω → BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hhom : ∀ a b v, kin a b (legalIntensityDilation q ρ • v) =
      (legalIntensityDilation q ρ)^2 * kin a b v) (t : ℝ) :
    (∫ ω, unclampedBlockLegalTilted q id id 1 kin g t
      (mapBlockData (legalMarkedPointDilation q (legalIntensityDilation q ρ)
        (legalIntensityDilation_pos q hρ).ne') (arrays ω).1)
      (mapBlockData (legalMarkedPointDilation q (legalIntensityDilation q ρ)
        (legalIntensityDilation_pos q hρ).ne') (arrays ω).2) ∂P) /
      volume.real (originalCenteredPhysicalCubeRegion b (2*(legalIntensityDilation q ρ*R))) =
      ρ^(1-2/(q:ℝ)) *
        ((∫ ω, unclampedBlockLegalTilted q id id 1 kin g (t*ρ^(2/(q:ℝ)))
          (arrays ω).1 (arrays ω).2 ∂P) /
          volume.real (originalCenteredPhysicalCubeRegion b (2*R))) := by
  rw [normalized_integral_unclampedBlockLegalTilted_one_dilation P arrays kin g b
    (legalIntensityDilation_pos q hρ) hR hhom t]
  have hfactor := legalIntensityDilation_kinetic_scale hq hρ
  rw [abs_of_pos (inv_pos.mpr (pow_pos (legalIntensityDilation_pos q hρ) q))] at hfactor
  rw [hfactor]
  simp only [div_eq_mul_inv,legalIntensityDilation_inverse_square hρ]

/-- A fixed positive physical dilation preserves the full large-radius limit;
it does not select a new subsequence of finite windows. -/
theorem tendsto_originalPressure_positive_dilation_iff
    {f : ℝ → ℝ} {c L : ℝ} (hc : 0 < c) :
    Tendsto (fun R ↦ f (c*R)) atTop (𝓝 L) ↔ Tendsto f atTop (𝓝 L) := by
  constructor
  · intro h
    have := h.comp (tendsto_id.const_mul_atTop (inv_pos.mpr hc))
    simpa only [Function.comp_def,id_eq,mul_inv_cancel_left₀ hc.ne'] using this
  · intro h
    exact h.comp (tendsto_id.const_mul_atTop hc)

end OTSelector.Reconstruction

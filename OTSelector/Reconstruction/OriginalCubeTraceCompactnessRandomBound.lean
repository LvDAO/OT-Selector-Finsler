import OTSelector.Reconstruction.OriginalCubeTraceCompactnessDualBound

/-! Measurable common random bounds built from literal spatial face data. -/
open Set Function Filter MeasureTheory BoxIntegral
open scoped ENNReal Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- The literal common bound is measurable for every jointly measurable
scene/face scalar field; it contains only original finite cell integrals. -/
theorem measurable_originalDyadicTraceDualBound
    {Ω : Type*} [MeasurableSpace Ω] {q : ℕ}
    {g : Ω → (Fin q → ℝ) → ℝ}
    (hg : Measurable (fun p : Ω × (Fin q → ℝ) ↦ g p.1 p.2)) (n : ℕ) :
    Measurable (fun ω ↦ originalDyadicTraceDualBound (g ω) n) := by
  classical
  unfold originalDyadicTraceDualBound
  have hbulk : Measurable (fun ω ↦ ∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1),
      (g ω y)^2) := (hg.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hcell (J : (originalDyadicFacePartition (ι := Fin q) n).boxes) :
      Measurable (fun ω ↦ (∫ y in J.1.Icc, g ω y)^2) :=
    hg.stronglyMeasurable.integral_prod_right'.measurable.pow_const 2
  exact hbulk.const_mul _ |>.add
    ((Finset.measurable_sum Finset.univ (fun J _ ↦ hcell J)).const_mul _)

/-- Product-square-integrability gives one full-measure scene set on which
the common literal bound controls all smooth tests simultaneously. -/
theorem ae_all_smooth_trace_pairing_sq_le_originalDyadicTraceDualBound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] {q : ℕ}
    {g : Ω → (Fin q → ℝ) → ℝ}
    (hg : Measurable (fun p : Ω × (Fin q → ℝ) ↦ g p.1 p.2))
    (hg2 : Integrable (fun p : Ω × (Fin q → ℝ) ↦ (g p.1 p.2)^2)
      (μ.prod (volume.restrict (Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1)))))
    (n : ℕ) :
    ∀ᵐ ω ∂μ, ∀ (f : (Fin q → ℝ) × ℝ → ℝ), ContDiff ℝ 1 f →
      (∫ p in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1, f p) = 0 →
      boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1 ≤ 1 →
      (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1), g ω y * f (y, 0))^2 ≤
        originalDyadicTraceDualBound (g ω) n := by
  filter_upwards [hg2.prod_right_ae] with ω hω
  have hgm : AEStronglyMeasurable (g ω)
      (volume.restrict (Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1))) :=
    (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hLp := (memLp_two_iff_integrable_sq hgm).mpr hω
  exact fun f hf hmean henergy ↦
    smooth_unit_energy_trace_pairing_sq_le_originalDyadicTraceDualBound hLp hf hmean henergy n

/-- The actual common random bound is integrable as soon as its literal
finite-cell second moments are integrable; no supremum measurability is needed. -/
theorem integrable_originalDyadicTraceDualBound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] {q : ℕ}
    {g : Ω → (Fin q → ℝ) → ℝ}
    (hg2 : Integrable (fun p : Ω × (Fin q → ℝ) ↦ (g p.1 p.2)^2)
      (μ.prod (volume.restrict (Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1)))))
    (n : ℕ)
    (hcell : ∀ J : (originalDyadicFacePartition (ι := Fin q) n).boxes,
      Integrable (fun ω ↦ (∫ y in J.1.Icc, g ω y)^2) μ) :
    Integrable (fun ω ↦ originalDyadicTraceDualBound (g ω) n) μ := by
  unfold originalDyadicTraceDualBound
  exact (hg2.integral_prod_left.const_mul _).add
    ((integrable_finsetSum Finset.univ (fun J _ ↦ hcell J)).const_mul _)

/-- The expectation is exactly the original face second moment plus finitely
many original cell-average second moments. Fubini exposes the stationary
bulk term without requiring any rate or mixing input. -/
theorem integral_originalDyadicTraceDualBound_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] {q : ℕ}
    {g : Ω → (Fin q → ℝ) → ℝ}
    (hg2 : Integrable (fun p : Ω × (Fin q → ℝ) ↦ (g p.1 p.2)^2)
      (μ.prod (volume.restrict (Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1)))))
    (n : ℕ)
    (hcell : ∀ J : (originalDyadicFacePartition (ι := Fin q) n).boxes,
      Integrable (fun ω ↦ (∫ y in J.1.Icc, g ω y)^2) μ) :
    (∫ ω, originalDyadicTraceDualBound (g ω) n ∂μ) =
      2 * ((q + 2 : ℕ) : ℝ) * ((1 : ℝ) / 2^n) *
        (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1), ∫ ω, (g ω y)^2 ∂μ) +
      2 * (Fintype.card (originalDyadicFacePartition (ι := Fin q) n).boxes : ℝ) *
        ((((1 : ℝ) / 2^n)^(q + 1))⁻¹ * (((q + 1 : ℕ) : ℝ) / 2)) *
          (∑ J : (originalDyadicFacePartition (ι := Fin q) n).boxes,
            ∫ ω, (∫ y in J.1.Icc, g ω y)^2 ∂μ) := by
  unfold originalDyadicTraceDualBound
  rw [integral_add (hg2.integral_prod_left.const_mul _)
      ((integrable_finsetSum Finset.univ (fun J _ ↦ hcell J)).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_finsetSum Finset.univ (fun J _ ↦ hcell J)]
  rw [integral_integral_swap hg2]

end OTSelector.Reconstruction

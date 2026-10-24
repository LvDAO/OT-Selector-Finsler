import OTSelector.Probability.CavityGridPhaseHaar
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-! Signed source-cell readouts under the actual normalized Ioc phase law. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability
variable (ι : Type*) [Fintype ι] (ell : ℝ) [h : Fact (0 < ell)]

/-- Absolute integrability and exact signed periodization for the actual phase law. -/
theorem integrable_integral_cavityGridPhaseLaw_periodization
    (W : (ι → ℝ) → ℝ) (hW : Measurable W)
    (hi : Integrable W (volume : Measure (ι → ℝ))) :
    Integrable (fun u ↦ ∑' g : CavityGridLattice ι ell, W (g +ᵥ u))
        (cavityGridPhaseLaw ι ell) ∧
      (∫ u, ∑' g : CavityGridLattice ι ell, W (g +ᵥ u)
        ∂cavityGridPhaseLaw ι ell) =
        ((ENNReal.ofReal ell ^ Fintype.card ι)⁻¹).toReal * ∫ x, W x := by
  let P := cavityGridPhaseLaw ι ell
  have hm (g : CavityGridLattice ι ell) : Measurable (fun u ↦ W (g +ᵥ u)) :=
    hW.comp (measurable_const_vadd g)
  have hn : (∑' g : CavityGridLattice ι ell, ∫⁻ u, ‖W (g +ᵥ u)‖ₑ ∂P) < ∞ := by
    rw [← lintegral_tsum (fun g ↦ (hm g).enorm.aemeasurable)]
    rw [lintegral_cavityGridPhaseLaw_periodization ι ell (fun x ↦ ‖W x‖ₑ) hW.enorm]
    apply ENNReal.mul_lt_top
    · exact ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr
        (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr h.out))))
    · exact hi.hasFiniteIntegral.lt_top
  have hsum : Measurable (fun u ↦ ∑' g : CavityGridLattice ι ell, W (g +ᵥ u)) :=
    Measurable.tsum hm
  refine ⟨⟨hsum.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_enorm]
    apply lt_of_le_of_lt (lintegral_mono (fun u ↦ enorm_tsum_le_tsum_enorm))
    rwa [lintegral_tsum (fun g ↦ (hm g).enorm.aemeasurable)]
  · rw [integral_tsum (fun g ↦ (hm g).aestronglyMeasurable) hn.ne]
    simp only [P, cavityGridPhaseLaw, ProbabilityTheory.cond, integral_smul_measure,
      volume_cavityGridPhaseCell, smul_eq_mul]
    rw [tsum_mul_left]
    congr 1
    exact (isAddFundamentalDomain_cavityGridPhaseCell ι ell h.out).integral_eq_tsum'' W hi |>.symm

/-- The signed identity retains an arbitrary dependent original environment.
Its absolute convergence is derived from the whole spatial/environment L1 bound. -/
theorem integrable_integral_cavityGridPhaseLaw_prod_periodization
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [SFinite η]
    (F : (ι → ℝ) × Ω → ℝ) (hF : Measurable F)
    (hi : Integrable F ((volume : Measure (ι → ℝ)).prod η)) :
    Integrable (fun p : (ι → ℝ) × Ω ↦
      ∑' g : CavityGridLattice ι ell, F (g +ᵥ p.1, p.2))
        ((cavityGridPhaseLaw ι ell).prod η) ∧
      (∫ p : (ι → ℝ) × Ω,
        ∑' g : CavityGridLattice ι ell, F (g +ᵥ p.1, p.2)
        ∂(cavityGridPhaseLaw ι ell).prod η) =
        ((ENNReal.ofReal ell ^ Fintype.card ι)⁻¹).toReal *
          ∫ p, F p ∂(volume : Measure (ι → ℝ)).prod η := by
  let P := cavityGridPhaseLaw ι ell
  let T (g : CavityGridLattice ι ell) (p : (ι → ℝ) × Ω) := F (g +ᵥ p.1, p.2)
  have hm (g : CavityGridLattice ι ell) : Measurable (T g) :=
    hF.comp ((measurable_const_vadd g).comp measurable_fst |>.prodMk measurable_snd)
  have hn : (∑' g, ∫⁻ p, ‖T g p‖ₑ ∂P.prod η) < ∞ := by
    rw [← lintegral_tsum (fun g ↦ (hm g).enorm.aemeasurable)]
    rw [lintegral_prod_symm _ (Measurable.tsum (fun g ↦ (hm g).enorm)).aemeasurable]
    simp_rw [show ∀ s, (∫⁻ u, ∑' g, ‖T g (u, s)‖ₑ ∂P) =
        (ENNReal.ofReal ell ^ Fintype.card ι)⁻¹ * ∫⁻ x, ‖F (x, s)‖ₑ by
      intro s
      exact lintegral_cavityGridPhaseLaw_periodization ι ell _
        (hF.enorm.comp (measurable_id.prodMk measurable_const))]
    rw [lintegral_const_mul' _ _]
    rotate_left
    · exact (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr
        (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr h.out))))).ne
    rw [← lintegral_prod_symm _ hF.enorm.aemeasurable]
    apply ENNReal.mul_lt_top
    · exact ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr
        (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr h.out))))
    · exact hi.hasFiniteIntegral.lt_top
  have hTi (g : CavityGridLattice ι ell) : Integrable (T g) (P.prod η) := by
    refine ⟨(hm g).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt (ENNReal.le_tsum g) hn
  have hsum : Measurable (fun p ↦ ∑' g, T g p) := Measurable.tsum hm
  have hsumInt : Integrable (fun p ↦ ∑' g, T g p) (P.prod η) := by
    refine ⟨hsum.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    apply lt_of_le_of_lt (lintegral_mono (fun p ↦ enorm_tsum_le_tsum_enorm))
    rwa [lintegral_tsum (fun g ↦ (hm g).enorm.aemeasurable)]
  refine ⟨hsumInt, ?_⟩
  let W : (ι → ℝ) → ℝ := fun x ↦ ∫ s, F (x, s) ∂η
  have hW : Measurable W := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hWi : Integrable W (volume : Measure (ι → ℝ)) := hi.integral_prod_left
  have hphase := integrable_integral_cavityGridPhaseLaw_periodization ι ell W hW hWi
  rw [integral_tsum (fun g ↦ (hm g).aestronglyMeasurable) hn.ne]
  have heq (g : CavityGridLattice ι ell) :
      (∫ p, T g p ∂P.prod η) = ∫ u, W (g +ᵥ u) ∂P := integral_prod _ (hTi g)
  simp_rw [heq]
  have hnorm : (∑' g : CavityGridLattice ι ell, ∫⁻ u, ‖W (g +ᵥ u)‖ₑ ∂P) ≠ ∞ := by
    apply ne_of_lt
    have habs (g : CavityGridLattice ι ell) :
        (∫⁻ u, ‖W (g +ᵥ u)‖ₑ ∂P) ≤ ∫⁻ p, ‖T g p‖ₑ ∂P.prod η := by
      rw [lintegral_prod _ (hm g).enorm.aemeasurable]
      apply lintegral_mono
      intro u
      exact enorm_integral_le_lintegral_enorm _
    exact lt_of_le_of_lt (ENNReal.tsum_le_tsum habs) hn
  rw [← integral_tsum (f := fun g u ↦ W (g +ᵥ u))
    (fun g ↦ (hW.comp (measurable_const_vadd g)).aestronglyMeasurable) hnorm]
  rw [hphase.2]
  congr 1
  exact (integral_prod F hi).symm

end OTSelector.Probability

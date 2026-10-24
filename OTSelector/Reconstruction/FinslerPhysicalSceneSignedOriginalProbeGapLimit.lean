import OTSelector.Reconstruction.FinslerPhysicalSceneRealProbeIntegralFreezing
import Mathlib.Order.Filter.Curry

/-!
# Same-plan convolution recovery preserves expected original signed gaps

Uniform freezing is applied before averaging, so neither uniform integrability
nor a coupling of changing original experiments is needed.
-/
open Set Function Filter MeasureTheory
open scoped Topology CompactlySupported ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι M I : Type*} [Fintype ι] [MeasurableSpace M]
local notation "V" => (ι → ℝ)

/-- Vanishing same-plan convolution gaps recover the original signed probe
on the same index filter. In particular, this preserves curried two-stage
convergence on changing original finite experiments. -/
theorem tendsto_expected_original_real_macroProbe_gap_zero_of_convolution_gap
    {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)] {L : Filter I}
    (R : ∀ i, Measure (Ω i)) (hR : ∀ i, R i univ ≤ 1)
    (Γp Γm : ∀ i, Ω i → Measure (M × M))
    [∀ i ω, IsFiniteMeasure (Γp i ω)] [∀ i ω, IsFiniteMeasure (Γm i ω)]
    (hΓp : ∀ i, ∀ᵐ ω ∂R i, Γp i ω univ ≤ 1)
    (hΓm : ∀ i, ∀ᵐ ω ∂R i, Γm i ω univ ≤ 1)
    (coord : I → M → V) (hcoord : ∀ i, Measurable (coord i))
    (u : M → ℝ) (hu : Measurable u)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    (sample : I → ℕ) (hsample : Tendsto sample L atTop)
    (η : C_c(V, ℝ)) (hη : ∀ v, 0 ≤ η v) (hηmass : (∫ v, η v ∂volume) = 1)
    (g : C_c(V × (ℝ × ℝ), ℝ))
    (hconv : Tendsto (fun i ↦ ∫⁻ ω, ENNReal.ofReal
      |(∫ p, ∫ v, η v * g ((scale (sample i))⁻¹ • (coord i p.1 - v), (u p.1, u p.2))
          ∂volume ∂Γp i ω) -
        ∫ p, ∫ v, η v * g ((scale (sample i))⁻¹ • (coord i p.1 - v), (u p.1, u p.2))
          ∂volume ∂Γm i ω| ∂R i) L (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁻ ω, ENNReal.ofReal
      |(∫ p, g ((scale (sample i))⁻¹ • coord i p.1, (u p.1, u p.2)) ∂Γp i ω) -
        ∫ p, g ((scale (sample i))⁻¹ • coord i p.1, (u p.1, u p.2)) ∂Γm i ω| ∂R i)
      L (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hε
  simp only [zero_add] at hδε
  let α : ℝ := (δ : ℝ) / 3
  have hα : 0 < α := div_pos (by exact_mod_cast hδ) (by norm_num)
  have hαe : 0 < ENNReal.ofReal α := ENNReal.ofReal_pos.mpr hα
  have hfreeze := hsample.eventually
    (eventually_uniform_plan_real_macro_probe_convolution_bound
      (Z := M × M) g η hη hηmass scale hscalePos hscale hα)
  filter_upwards [hfreeze, ENNReal.tendsto_nhds_zero.mp hconv _ hαe] with i hi hci
  let x : M × M → V := fun p ↦ (scale (sample i))⁻¹ • coord i p.1
  let clock : M × M → ℝ × ℝ := fun p ↦ (u p.1, u p.2)
  have hx : Measurable x := (measurable_const_smul _).comp ((hcoord i).comp measurable_fst)
  have hclock : Measurable clock := (hu.comp measurable_fst).prodMk (hu.comp measurable_snd)
  let C : Ω i → ℝ := fun ω ↦
    |(∫ p, ∫ v, η v * g ((scale (sample i))⁻¹ • (coord i p.1 - v), clock p)
        ∂volume ∂Γp i ω) -
      ∫ p, ∫ v, η v * g ((scale (sample i))⁻¹ • (coord i p.1 - v), clock p)
        ∂volume ∂Γm i ω|
  have hb : (∫⁻ ω, ENNReal.ofReal
      |(∫ p, g (x p, clock p) ∂Γp i ω) - ∫ p, g (x p, clock p) ∂Γm i ω| ∂R i) ≤
      (∫⁻ ω, ENNReal.ofReal (C ω) ∂R i) + ENNReal.ofReal α + ENNReal.ofReal α := by
    have hpoint : ∀ᵐ ω ∂R i,
        ENNReal.ofReal |(∫ p, g (x p, clock p) ∂Γp i ω) -
          ∫ p, g (x p, clock p) ∂Γm i ω| ≤
        ENNReal.ofReal (C ω) + ENNReal.ofReal α + ENNReal.ofReal α := by
      filter_upwards [hΓp i, hΓm i] with ω hp hm
      have hmass (π : Measure (M × M)) (hπ : π univ ≤ 1) : π.real univ ≤ 1 := by
        simpa only [measureReal_def, ENNReal.toReal_one] using
          ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) hπ
      have hbp := (hi (Γp i ω) x hx clock hclock).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hmass _ hp) hα.le)
      have hbm := (hi (Γm i ω) x hx clock hclock).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hmass _ hm) hα.le)
      have ht := abs_sub_le
        (∫ p, g (x p, clock p) ∂Γp i ω)
        (∫ p, ∫ v, η v * g (x p - (scale (sample i))⁻¹ • v, clock p) ∂volume ∂Γp i ω)
        (∫ p, g (x p, clock p) ∂Γm i ω)
      have ht' := abs_sub_le
        (∫ p, ∫ v, η v * g (x p - (scale (sample i))⁻¹ • v, clock p) ∂volume ∂Γp i ω)
        (∫ p, ∫ v, η v * g (x p - (scale (sample i))⁻¹ • v, clock p) ∂volume ∂Γm i ω)
        (∫ p, g (x p, clock p) ∂Γm i ω)
      rw [abs_sub_comm] at hbp
      have hr : |(∫ p, g (x p, clock p) ∂Γp i ω) -
          ∫ p, g (x p, clock p) ∂Γm i ω| ≤ C ω + α + α := by
        dsimp only [C]
        simp only [smul_sub] at *
        linarith
      calc
        _ ≤ ENNReal.ofReal (C ω + α + α) := ENNReal.ofReal_le_ofReal hr
        _ = _ := by
          rw [ENNReal.ofReal_add (add_nonneg (abs_nonneg _) hα.le) hα.le,
            ENNReal.ofReal_add (abs_nonneg _) hα.le]
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal (C ω) + ENNReal.ofReal α + ENNReal.ofReal α ∂R i :=
        lintegral_mono_ae hpoint
      _ = (∫⁻ ω, ENNReal.ofReal (C ω) ∂R i) +
          ENNReal.ofReal α * R i univ + ENNReal.ofReal α * R i univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_add_right _ measurable_const,
          lintegral_const]
      _ ≤ _ := add_le_add (add_le_add le_rfl (by
        simpa only [mul_one, one_mul, mul_comm] using mul_le_mul_right (hR i) (ENNReal.ofReal α))) (by
          simpa only [mul_one, one_mul, mul_comm] using mul_le_mul_right (hR i) (ENNReal.ofReal α))
  have heq : ENNReal.ofReal α + ENNReal.ofReal α + ENNReal.ofReal α = (δ : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_add hα.le hα.le,
      ← ENNReal.ofReal_add (add_nonneg hα.le hα.le) hα.le]
    have hr : α + α + α = (δ : ℝ) := by dsimp only [α]; ring
    rw [hr, ENNReal.ofReal_coe_nnreal]
  exact hb.trans ((add_le_add (add_le_add hci le_rfl) le_rfl).trans (heq.le.trans hδε.le))

end OTSelector.Reconstruction

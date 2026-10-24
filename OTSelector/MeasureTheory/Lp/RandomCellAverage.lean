import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
## Lemma skeleton

* **Conditions:** Finite spatial measure, a probability sample law, jointly measurable scalar representatives of a uniformly bounded family in Hilbert L2; the final norm identity also assumes Bochner integrability of that family.
* **Objects:** Covariance and squared-average integrability, squared expectation equal to the squared Hilbert norm of the Bochner average, and measurable averages.
* **Proof detail:** Use Cauchy–Schwarz for each covariance, Fubini on the triple product, expand the squared spatial integral into a double product integral, and commute bounded bilinear inner products with Bochner integration.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 8A, Theorem 8.11, p. 218; Example 8.14, p. 219 (L2 Cauchy–Schwarz).
  https://measure.axler.net/MIRA.pdf#page=233
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 5B, Theorem 5.32 (Fubini), pp. 132–133.
  https://measure.axler.net/MIRA.pdf#page=147
* D. H. Fremlin, *Measure Theory, Volume 2*, Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46

**Relationship to the sources:** Derived Hilbert-valued averaging identity. The joint representatives and finite measure assumptions are explicit; no independence across spatial labels is supplied.
-/

/-! Literal random finite-cell averages and their actual Hilbert L2 second moments. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- The chosen representative of an actual scalar L2 vector has exactly its original square norm. -/
theorem integral_sq_L2_representative {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (x : Lp ℝ 2 μ) : (∫ ω, (x ω)^2 ∂μ) = ‖x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω ↦ by simp [sq])

/-- A jointly measurable realization of a uniformly bounded L2 family has
an actual covariance Fubini integral, without bounded sample values. -/
theorem integrable_finiteCell_covariance
    {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (ν : Measure Y) [IsFiniteMeasure ν] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Y → Lp ℝ 2 μ} {X : Y → Ω → ℝ}
    (hX : Measurable (Function.uncurry X))
    (hrep : ∀ y, X y =ᵐ[μ] (F y : Ω → ℝ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, ‖F y‖ ≤ C) :
    Integrable (fun p : (Y × Y) × Ω ↦ X p.1.1 p.2 * X p.1.2 p.2)
      ((ν.prod ν).prod μ) := by
  have hLp (y : Y) : MemLp (X y) 2 μ := (memLp_congr_ae (hrep y)).mpr (Lp.memLp (F y))
  have hprod (y z : Y) : Integrable (fun ω ↦ X y ω * X z ω) μ :=
    (hLp y).integrable_mul (hLp z)
  have hmean (y : Y) : (∫ ω, (X y ω)^2 ∂μ) ≤ C^2 := by
    calc
      _ = ∫ ω, ((F y) ω)^2 ∂μ := integral_congr_ae ((hrep y).fun_comp (fun r : ℝ ↦ r^2))
      _ = ‖F y‖^2 := integral_sq_L2_representative _
      _ ≤ C^2 := (sq_le_sq₀ (norm_nonneg _) hC).mpr (hbound y)
  have hm : Measurable (fun p : (Y × Y) × Ω ↦ X p.1.1 p.2 * X p.1.2 p.2) :=
    (hX.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hX.comp (measurable_fst.snd.prodMk measurable_snd))
  have hn (y z : Y) : (∫ ω, ‖X y ω * X z ω‖ ∂μ) ≤ C^2 := by
    calc
      _ ≤ ∫ ω, ((X y ω)^2 + (X z ω)^2) / 2 ∂μ := by
        apply integral_mono (hprod y z).norm (((hLp y).integrable_sq.add (hLp z).integrable_sq).div_const 2)
        intro ω
        change ‖X y ω * X z ω‖ ≤ ((X y ω)^2 + (X z ω)^2) / 2
        rw [Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|X y ω| - |X z ω|), sq_abs (X y ω), sq_abs (X z ω)]
      _ = ((∫ ω, (X y ω)^2 ∂μ) + ∫ ω, (X z ω)^2 ∂μ) / 2 := by
        rw [integral_div, integral_add (hLp y).integrable_sq (hLp z).integrable_sq]
      _ ≤ C^2 := by linarith [hmean y, hmean z]
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun p ↦ hprod p.1 p.2), ?_⟩
  apply Integrable.of_bound hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable (C^2)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
  exact hn p.1 p.2

/-- The literal random cell average square is integrable under the original law. -/
theorem integrable_sq_finiteCell_average
    {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (ν : Measure Y) [IsFiniteMeasure ν] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Y → Lp ℝ 2 μ} {X : Y → Ω → ℝ}
    (hX : Measurable (Function.uncurry X))
    (hrep : ∀ y, X y =ᵐ[μ] (F y : Ω → ℝ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, ‖F y‖ ≤ C) :
    Integrable (fun ω ↦ (∫ y, X y ω ∂ν)^2) μ := by
  have hi := (integrable_finiteCell_covariance ν μ hX hrep hC hbound).integral_prod_right
  convert hi using 1
  funext ω
  simpa only [pow_two] using (integral_prod_mul (μ := ν) (ν := ν)
    (fun y ↦ X y ω) (fun z ↦ X z ω)).symm

/-- The actual random cell integral has exactly the L2 second moment of its
Bochner orbit average. No pointwise interchange of an L2 representative is assumed. -/
theorem integral_sq_finiteCell_average_eq_norm_sq
    {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (ν : Measure Y) [IsFiniteMeasure ν] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Y → Lp ℝ 2 μ} {X : Y → Ω → ℝ}
    (hF : Integrable F ν) (hX : Measurable (Function.uncurry X))
    (hrep : ∀ y, X y =ᵐ[μ] (F y : Ω → ℝ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, ‖F y‖ ≤ C) :
    (∫ ω, (∫ y, X y ω ∂ν)^2 ∂μ) = ‖∫ y, F y ∂ν‖^2 := by
  have hi := integrable_finiteCell_covariance ν μ hX hrep hC hbound
  have hcov (y z : Y) : (∫ ω, X y ω * X z ω ∂μ) = inner ℝ (F y) (F z) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep y, hrep z] with ω hy hz
    simp [hy, hz, mul_comm]
  calc
    _ = ∫ ω, ∫ p : Y × Y, X p.1 ω * X p.2 ω ∂ν.prod ν ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ by
        simpa only [pow_two] using (integral_prod_mul (μ := ν) (ν := ν)
          (fun y ↦ X y ω) (fun z ↦ X z ω)).symm
    _ = ∫ p : Y × Y, ∫ ω, X p.1 ω * X p.2 ω ∂μ ∂ν.prod ν :=
      (integral_integral_swap hi).symm
    _ = ∫ y, ∫ z, ∫ ω, X y ω * X z ω ∂μ ∂ν ∂ν :=
      integral_prod _ hi.integral_prod_left
    _ = ∫ y, ∫ z, inner ℝ (F y) (F z) ∂ν ∂ν := by simp_rw [hcov]
    _ = ∫ y, inner ℝ (F y) (∫ z, F z ∂ν) ∂ν := by simp_rw [integral_inner (𝕜 := ℝ) hF]
    _ = inner ℝ (∫ y, F y ∂ν) (∫ z, F z ∂ν) := by
      simpa only [real_inner_comm] using integral_inner (𝕜 := ℝ) hF (∫ y, F y ∂ν)
    _ = _ := real_inner_self_eq_norm_sq _

/-- The literal random finite-cell integral is measurable in the original scene. -/
theorem measurable_finiteCell_average
    {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (ν : Measure Y) [SFinite ν] {X : Y → Ω → ℝ}
    (hX : Measurable (Function.uncurry X)) :
    Measurable (fun ω ↦ ∫ y, X y ω ∂ν) := by
  have hs : StronglyMeasurable (Function.uncurry (fun ω y ↦ X y ω)) :=
    (hX.comp measurable_swap).stronglyMeasurable
  exact hs.integral_prod_right.measurable

end OTSelector.Reconstruction

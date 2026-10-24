import OTSelector.MeasureTheory.DifferentiablePushforward
import OTSelector.Probability.CavityCells

/-!
# Original cavity allocation laws from actual differentials

For absolutely continuous insertion laws, locally Lipschitz costs with pairwise distinct
actual differentials have atomless differences. Their exact retained-input cavity cells
therefore partition the original insertion law and give every optimal partner's conditional
allocation probability. The original random variables, costs and vacancy prices are retained.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {E W Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace W] [MeasurableSpace Ω]
  {n : ℕ} (m : Measure E) [m.IsAddHaarMeasure]

private theorem nullSingletonClass_row_difference {U : Set E} (hU : IsOpen U)
    (μ : Measure E) (hμ : μ ≪ m) (hμU : ∀ᵐ x ∂μ, x ∈ U)
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g)
    {Lf Lg : ℝ≥0} (hLf : LipschitzOnWith Lf f U) (hLg : LipschitzOnWith Lg g U)
    (hne : ∀ᵐ x ∂m.restrict U, fderiv ℝ f x ≠ fderiv ℝ g x) :
    NullSingletonClass (μ.map (fun x ↦ f x - g x)) := by
  have hd : ∀ᵐ x ∂m.restrict U,
      DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ g x := by
    filter_upwards [hLf.ae_differentiableWithinAt (μ := m) hU.measurableSet,
      hLg.ae_differentiableWithinAt (μ := m) hU.measurableSet,
      ae_restrict_mem hU.measurableSet] with x hx hy hxU
    exact ⟨hx.differentiableAt (hU.mem_nhds hxU), hy.differentiableAt (hU.mem_nhds hxU)⟩
  apply Geometry.nullSingletonClass_map_of_ae_fderiv_ne_zero m hU.measurableSet
    (hf.sub hg) (hd.mono (fun x hx ↦ hx.1.sub hx.2)) _ μ hμ hμU
  filter_upwards [hd, hne] with x hx hnx
  rw [fderiv_sub hx.1 hx.2]
  exact sub_ne_zero.mpr hnx

/-- Distinct actual row-cost differentials give an almost surely unique original cavity
cell. Local Lipschitzness supplies differentiability; no atomless-law oracle is an input. -/
theorem ae_existsUnique_mem_cavityCell_of_indepFun_differentials
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure E) (hμ : μ ≪ m)
    {U : Set E} (hU : IsOpen U) (hμU : ∀ᵐ x ∂μ, x ∈ U)
    (W₀ : Ω → W) (X : Ω → E) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × E → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (n + 1))
    (hLip : ∀ᵐ w ∂P.map W₀, ∀ j, ∃ L, LipschitzOnWith L (fun x ↦ row (w, x) j) U)
    (hgrad : ∀ᵐ w ∂P.map W₀, ∀ j k, j ≠ k → ∀ᵐ x ∂m.restrict U,
      fderiv ℝ (fun s ↦ row (w, s) j) x ≠ fderiv ℝ (fun s ↦ row (w, s) k) x) :
    ∀ᵐ ω ∂P, ∃! j, (W₀ ω, X ω) ∈ cavityCell retained row i j := by
  apply ae_existsUnique_mem_cavityCell_of_indepFun_atomless P μ W₀ X hW hX hindep hlaw
    retained row hret hrow i
  filter_upwards [hLip, hgrad] with w hw hg
  intro j k hjk
  obtain ⟨Lj, hj⟩ := hw j
  obtain ⟨Lk, hk⟩ := hw k
  exact nullSingletonClass_row_difference m hU μ hμ hμU
    ((hrow j).comp (measurable_const.prodMk measurable_id))
    ((hrow k).comp (measurable_const.prodMk measurable_id)) hj hk (hg j k hjk)

/-- The original conditional allocation formula follows from local differential geometry
for every optimal assignment, without choosing or assuming a unique full optimizer. -/
theorem measure_optimal_partner_restrict_retained_differentials
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure E) [SFinite μ] (hμ : μ ≪ m)
    {U : Set E} (hU : IsOpen U) (hμU : ∀ᵐ x ∂μ, x ∈ U)
    (W₀ : Ω → W) (X : Ω → E) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × E → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i j : Fin (n + 1))
    (hLip : ∀ᵐ w ∂P.map W₀, ∀ k, ∃ L, LipschitzOnWith L (fun x ↦ row (w, x) k) U)
    (hgrad : ∀ᵐ w ∂P.map W₀, ∀ u v, u ≠ v → ∀ᵐ x ∂m.restrict U,
      fderiv ℝ (fun s ↦ row (w, s) u) x ≠ fderiv ℝ (fun s ↦ row (w, s) v) x)
    (σ : Ω → Assignment (n + 1))
    (hσ : ∀ᵐ ω ∂P, OptimalAssignment
      (Function.update (retained (W₀ ω)) i (row (W₀ ω, X ω))) (σ ω))
    (B : Set W) (hB : MeasurableSet B) :
    P {ω | W₀ ω ∈ B ∧ σ ω i = j} =
      ∫⁻ w in B, cavityCellMass μ retained row i j w ∂P.map W₀ := by
  apply measure_optimal_partner_restrict_retained_atomless P μ W₀ X hW hX hindep hlaw
    retained row hret hrow i j _ σ hσ B hB
  filter_upwards [hLip, hgrad] with w hw hg
  intro u v huv
  obtain ⟨Lu, hu⟩ := hw u
  obtain ⟨Lv, hv⟩ := hw v
  exact nullSingletonClass_row_difference m hU μ hμ hμU
    ((hrow u).comp (measurable_const.prodMk measurable_id))
    ((hrow v).comp (measurable_const.prodMk measurable_id)) hu hv (hg u v huv)

end OTSelector.Probability

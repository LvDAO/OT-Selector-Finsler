import OTSelector.Transport.EmpiricalSelector.CompactSupport
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! Quadratic transport cost errors under two uniformly close quantizers. -/
open MeasureTheory Set
noncomputable section
namespace OTSelector.Reconstruction

/-- A one-sided quadratic error only needs a bound on the original distance. -/
lemma half_square_le_half_square_add_quantization_error
    {a b D h : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (haD : a ≤ D) (hab : a ≤ b + 2 * h) :
    a ^ 2 / 2 ≤ b ^ 2 / 2 + 2 * D * h := by
  have hD : 0 ≤ D := ha.trans haD
  by_cases hab' : a ≤ b
  · nlinarith [sq_nonneg (b - a), mul_nonneg hD hh]
  · have hba : b ≤ a := le_of_not_ge hab'
    have hp := mul_le_mul (show a - b ≤ 2 * h by linarith)
      (show a + b ≤ 2 * D by linarith) (by positivity : 0 ≤ a + b)
      (by positivity : 0 ≤ 2 * h)
    nlinarith

variable {E : Type*} [NormedAddCommGroup E]

/-- Perturbing both endpoints by at most `h` changes half the squared distance
by at most `2 * D * h` from above when the original distance is at most `D`. -/
lemma quadratic_cost_le_quantized_cost_add_error
    {x y tx sy : E} {D h : ℝ} (hh : 0 ≤ h)
    (hxy : ‖y - x‖ ≤ D) (hx : ‖tx - x‖ ≤ h) (hy : ‖sy - y‖ ≤ h) :
    ‖y - x‖ ^ 2 / 2 ≤ ‖sy - tx‖ ^ 2 / 2 + 2 * D * h := by
  have hdist : ‖y - x‖ ≤ ‖sy - tx‖ + 2 * h := by
    calc
      ‖y - x‖ = ‖(y - sy) + (sy - tx) + (tx - x)‖ := by congr 1; abel
      _ ≤ ‖y - sy‖ + ‖sy - tx‖ + ‖tx - x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖sy - tx‖ + 2 * h := by rw [norm_sub_rev y sy]; linarith
  exact half_square_le_half_square_add_quantization_error
    (norm_nonneg _) (norm_nonneg _) hh hxy hdist

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Every genuine lift pays the literal quadratic grid cost plus a vanishing
error. Both real integrals are proved integrable on the original compact carrier. -/
theorem quadratic_coupling_lift_cost_bound
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : Set E} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) (hν : ∀ᵐ y ∂ν, y ∈ K)
    {T S : E → E} (hT : Measurable T) (hS : Measurable S)
    {h : ℝ} (hh : 0 ≤ h)
    (hTx : ∀ x ∈ K, ‖T x - x‖ ≤ h) (hSy : ∀ y ∈ K, ‖S y - y‖ ≤ h)
    {π κ : Measure (E × E)} (hπ : Vlasov.IsCoupling π μ ν)
    (hmap : π.map (Prod.map T S) = κ) :
    Integrable (fun z : E × E ↦ ‖z.2 - z.1‖ ^ 2 / 2) π ∧
    Integrable (fun z : E × E ↦ ‖z.2 - z.1‖ ^ 2 / 2) κ ∧
    (∫ z : E × E, ‖z.2 - z.1‖ ^ 2 / 2 ∂π) ≤
      (∫ z : E × E, ‖z.2 - z.1‖ ^ 2 / 2 ∂κ) + 2 * Metric.diam K * h := by
  have : IsProbabilityMeasure (π.map Prod.fst) := by rw [hπ.1]; infer_instance
  have : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  have hx : ∀ᵐ z ∂π, z.1 ∈ K := ae_of_ae_map measurable_fst.aemeasurable (by
    rwa [hπ.1])
  have hy : ∀ᵐ z ∂π, z.2 ∈ K := ae_of_ae_map measurable_snd.aemeasurable (by
    rwa [hπ.2])
  let c : E × E → ℝ := fun z ↦ ‖z.2 - z.1‖ ^ 2 / 2
  have hc : Measurable c := by
    exact ((measurable_snd.sub measurable_fst).norm.pow_const 2).div_const 2
  have hcg : Measurable (c ∘ Prod.map T S) := hc.comp (hT.prodMap hS)
  have hD : 0 ≤ Metric.diam K := Metric.diam_nonneg
  have hnorm : ∀ᵐ z ∂π, ‖z.2 - z.1‖ ≤ Metric.diam K := by
    filter_upwards [hx, hy] with z hz₁ hz₂
    simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hK.isBounded hz₂ hz₁
  have hgrid : ∀ᵐ z ∂π, ‖S z.2 - T z.1‖ ≤ Metric.diam K + 2 * h := by
    filter_upwards [hx, hy, hnorm] with z hz₁ hz₂ hzD
    calc
      ‖S z.2 - T z.1‖ = ‖(S z.2 - z.2) + (z.2 - z.1) + (z.1 - T z.1)‖ :=
        by congr 1; abel
      _ ≤ ‖S z.2 - z.2‖ + ‖z.2 - z.1‖ + ‖z.1 - T z.1‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ Metric.diam K + 2 * h := by
        rw [norm_sub_rev z.1 (T z.1)]
        linarith [hTx z.1 hz₁, hSy z.2 hz₂]
  have hci : Integrable c π := (integrable_const (Metric.diam K ^ 2 / 2)).mono'
      hc.aestronglyMeasurable (by
    filter_upwards [hnorm] with z hz
    dsimp [c]
    rw [abs_of_nonneg (by positivity)]
    nlinarith [norm_nonneg (z.2 - z.1)])
  have hcgi : Integrable (c ∘ Prod.map T S) π :=
    (integrable_const ((Metric.diam K + 2 * h) ^ 2 / 2)).mono'
      hcg.aestronglyMeasurable (by
    filter_upwards [hgrid] with z hz
    dsimp [c]
    rw [abs_of_nonneg (by positivity)]
    nlinarith [norm_nonneg (S z.2 - T z.1)])
  have hcki : Integrable c κ := by
    rw [← hmap]
    exact (integrable_map_measure hc.aestronglyMeasurable (hT.prodMap hS).aemeasurable).2 hcgi
  refine ⟨hci, hcki, ?_⟩
  have heq : ∫ z, c z ∂κ = ∫ z, c (Prod.map T S z) ∂π := by
    rw [← hmap]
    exact integral_map (hT.prodMap hS).aemeasurable hc.aestronglyMeasurable
  rw [show (fun z : E × E ↦ ‖z.2 - z.1‖ ^ 2 / 2) = c from rfl, heq]
  calc
    (∫ z, c z ∂π) ≤ ∫ z, c (Prod.map T S z) + 2 * Metric.diam K * h ∂π := by
      apply integral_mono_ae hci (hcgi.add (integrable_const _))
      filter_upwards [hx, hy, hnorm] with z hz₁ hz₂ hzD
      exact quadratic_cost_le_quantized_cost_add_error hh hzD (hTx z.1 hz₁) (hSy z.2 hz₂)
    _ = (∫ z, c (Prod.map T S z) ∂π) + 2 * Metric.diam K * h := by
      have hcgi' : Integrable (fun z ↦ c (Prod.map T S z)) π := hcgi
      rw [integral_add hcgi' (integrable_const _)]; simp

end OTSelector.Reconstruction

import OTSelector.Reconstruction.EndpointWindowDeterminantMoments

/-!
# Returning the whole-interval moments to the original conditional clock

All endpoint windows use one fixed potential offset. The scalar shift is then
undone once, giving the moment under the original conditional law itself.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator MatrixOrder

namespace OTSelector.Reconstruction

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The two endpoint windows prove both moments directly under the original scalar
conditional law, with its actual potential-clock offset retained in the observable. -/
theorem originalClock_compliance_moments_of_endpoint_windows
    {K : ℝ → Matrix n n ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b l h c u₀ : ℝ}
    (WL : PhysicalJacobiMomentWindow K (μ.map (fun x ↦ x - u₀)) a l)
    (WR : PhysicalJacobiMomentWindow K (μ.map (fun x ↦ x - u₀)) h b)
    (hl : l < b) (hh : a < h)
    (hK : ContinuousOn K (Ioo a b))
    (hKpos : ∀ q ∈ Ioo a b, (K q).PosSemidef)
    (hc : c ∈ Ioo a b)
    (hμ : ∀ᵐ t ∂μ.map (fun x ↦ x - u₀), t ∈ Ioo a b) :
    Integrable (fun x ↦ (1 + CFC.abs (∫ q in c..(x - u₀), K q)).det) μ ∧
      ∀ r : ℝ, 0 < r → r < 2 →
        Integrable (fun x ↦ ‖∫ q in c..(x - u₀), K q‖ ^ r) μ := by
  obtain ⟨hdet, hpower⟩ := compliance_moments_of_endpoint_windows WL WR hl hh hK hKpos hc hμ
  exact ⟨hdet.comp_measurable (measurable_id.sub_const u₀),
    fun r hr0 hr ↦ (hpower r hr0 hr).comp_measurable (measurable_id.sub_const u₀)⟩

end OTSelector.Reconstruction

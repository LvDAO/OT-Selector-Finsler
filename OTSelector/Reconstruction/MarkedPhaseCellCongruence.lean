import OTSelector.LinearAlgebra.Matrix.MeasurablePhaseCongruence
import OTSelector.Reconstruction.MarkedPhaseSourceCellVolume
import OTSelector.LinearAlgebra.Matrix.CongruenceDeterminantBound

/-!
Conditions: A fixed matrix and a measurable matrix family, or a positive-semidefinite matrix for the positivity conclusion.

Objects: Measurability and positive semidefiniteness of T U T transpose.

Proof detail: Matrix multiplication is continuous/measurable; pull the quadratic form back by T transpose to preserve positivity.

Sources: Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48); D. H. Fremlin, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106).
Relation: Elementary congruence/readout adapters, not a residue or focal asymptotic claim.
-/

/-!
# Original marked phase-cell intensities under anisotropic compliance normalization

The same fixed real frame acts on the actual compliance by congruence. Its
marked source-cell intensity is bounded by a frame-dependent finite multiple of
the unchanged original determinant envelope, without an additional moment.
-/
open Set Function Matrix MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]





/-- One finite frame-dependent constant controls all original marked phase-cell intensities.
The original mark law and its complete input are retained. -/
theorem exists_prod_volume_markedPhaseSourceCell_congruence_bound (T : Matrix ι ι ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {L : Matrix ι ι ℝ}, IsUnit L.det →
      ∀ {U : ℝ → Matrix ι ι ℝ}, Measurable U → (∀ a, (U a).PosSemidef) →
      ∀ {c : ℝ → (ι → ℝ)}, Measurable c →
      ∀ {B : Set ℝ}, MeasurableSet B → ∀ (μ : Measure ℝ) [SFinite μ] (R : ℝ),
      ((volume : Measure (ι → ℝ)).prod μ)
          (markedPhaseSourceCell L (fun a ↦ T * U a * Tᵀ) c B R) ≤
        ENNReal.ofReal C * ((volume : Measure (ι → ℝ)).prod μ)
          (markedPhaseSourceCell L U c B R) := by
  obtain ⟨C, hC, hbound⟩ := OTSelector.Probability.exists_det_one_add_congruence_bound T
  refine ⟨C, hC, fun {L} hL {U} hUm hU {c} hc {B} hB μ _ R ↦ ?_⟩
  rw [prod_volume_markedPhaseSourceCell hL (measurable_phaseLegCongruence T hUm)
    (fun a ↦ phaseLegCongruence_posSemidef T (hU a)) hc hB μ R,
    prod_volume_markedPhaseSourceCell hL hUm hU hc hB μ R]
  have hI : (∫⁻ a, ENNReal.ofReal (B.indicator (fun a ↦ (1 + T * U a * Tᵀ).det) a) ∂μ) ≤
      ENNReal.ofReal C * ∫⁻ a, ENNReal.ofReal (B.indicator (fun a ↦ (1 + U a).det) a) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro a
    by_cases ha : a ∈ B
    · simp only [indicator_of_mem ha]
      rw [← ENNReal.ofReal_mul hC.le]
      exact ENNReal.ofReal_le_ofReal (hbound (U a) (hU a))
    · simp [ha]
  calc
    _ ≤ (ENNReal.ofReal |L.det| *
        volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R))) *
        (ENNReal.ofReal C * ∫⁻ a, ENNReal.ofReal
          (B.indicator (fun a ↦ (1 + U a).det) a) ∂μ) := by gcongr
    _ = _ := by ac_rfl

end OTSelector.Reconstruction

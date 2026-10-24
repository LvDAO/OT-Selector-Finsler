import OTSelector.Reconstruction.OriginalCubeTraceCompactnessCanonicalSmoothCube
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Countable Hilbert bases are intrinsic to the actual original closed cube-gradient space. -/
open Set Function MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- In a separable real inner-product space every actual orthonormal family is countable. -/
theorem countable_of_orthonormal_real {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [SeparableSpace H] {ι : Type*}
    {b : ι → H} (hb : Orthonormal ℝ b) : Countable ι := by
  apply Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (b i) (1 / 2 : ℝ))
  · intro i j hij
    apply Metric.ball_disjoint_ball
    have hs : ‖b i - b j‖^2 = 2 := by
      rw [norm_sub_sq_real, hb.norm_eq_one i, hb.norm_eq_one j, hb.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (b i - b j)]
  · exact fun _ ↦ Metric.isOpen_ball
  · exact fun i ↦ ⟨b i, Metric.mem_ball_self (by norm_num)⟩

/-- Genuine Hilbert-basis existence and separability supply a countable basis internally. -/
theorem exists_countable_real_hilbertBasis (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H] :
    ∃ w : Set H, w.Countable ∧ ∃ b : HilbertBasis w ℝ H, (b : w → H) = Subtype.val := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℝ H
  have hc : Countable w := countable_of_orthonormal_real b.orthonormal
  exact ⟨w, Set.countable_coe_iff.mp hc, b, hb⟩

/-- The actual original cube-gradient Hilbert closure has a countable orthonormal basis,
from separability of its genuine Euclidean-valued L2 ambient space. -/
theorem exists_countable_hilbertBasis_originalMeanZeroGradientClosure
    {q : ℕ} (K : Compacts (Fin q → ℝ)) (R : ℝ) :
    ∃ w : Set (originalGradientClosure (originalMeanZeroGradientLtwo K
      (volume.restrict (haarRootCube (Fin q) R)))), w.Countable ∧
      ∃ b : HilbertBasis w ℝ (originalGradientClosure (originalMeanZeroGradientLtwo K
        (volume.restrict (haarRootCube (Fin q) R)))),
        (b : w → originalGradientClosure (originalMeanZeroGradientLtwo K
          (volume.restrict (haarRootCube (Fin q) R)))) = Subtype.val := by
  let μ : Measure (Fin q → ℝ) := volume.restrict (haarRootCube (Fin q) R)
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp (EuclideanSpace ℝ (Fin q)) 2 μ) := inferInstance
  have : SecondCountableTopology (originalGradientClosure (originalMeanZeroGradientLtwo K μ)) :=
    inferInstanceAs (SecondCountableTopology
      {v : Lp (EuclideanSpace ℝ (Fin q)) 2 μ // v ∈ originalGradientClosure (originalMeanZeroGradientLtwo K μ)})
  exact exists_countable_real_hilbertBasis _

end OTSelector.Reconstruction

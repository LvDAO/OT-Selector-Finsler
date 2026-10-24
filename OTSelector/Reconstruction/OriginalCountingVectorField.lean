import OTSelector.Reconstruction.OriginalCountingFieldEverywhereLipschitz

/-! The actual coordinatewise infimum construction for arbitrary vector node data. -/
open Set Function MeasureTheory
open scoped NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false

variable {X Y ι : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [PseudoMetricSpace Y] [Fintype ι]

/-- Coordinatewise actual-node infima. Every absent original atom slot repeats
an actual occupied atom, and an empty actual measure gives the zero vector. -/
def originalCountingVectorField (base : X) (L : ℝ≥0) (z : X → Y) (p : X → ι → ℝ)
    (μ : LocalFiniteMeasure X) (x : Y) : ι → ℝ := fun i ↦
  originalCountingRoughField base L z (fun e ↦ p e i) μ x

theorem measurable_originalCountingVectorField
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (base : X) (L : ℝ≥0) (z : X → Y) (p : X → ι → ℝ)
    (hz : Measurable z) (hp : Measurable p) :
    Measurable (fun a : LocalFiniteMeasure X × Y ↦
      originalCountingVectorField base L z p a.1 a.2) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_originalCountingRoughField base L z (fun e ↦ p e i) hz
    ((measurable_pi_apply i).comp hp)

/-- The same global Lipschitz constant holds on every ambient original scene. -/
theorem lipschitzWith_originalCountingVectorField
    (base : X) (L : ℝ≥0) (z : X → Y) (p : X → ι → ℝ) (μ : LocalFiniteMeasure X) :
    LipschitzWith L (originalCountingVectorField base L z p μ) :=
  lipschitzWith_originalCountingRoughField_vector_everywhere base L z p μ

/-- The scalar one-sided error gives the same vector sup-norm error at every
actual occupied node; no coordinate factor or artificial node is introduced. -/
theorem originalCountingVectorField_node_error
    (base : X) (L : ℝ≥0) (z : X → Y) (p : X → ι → ℝ) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) {b : ℝ} (hb : 0 ≤ b)
    (hrough : ∀ e ∈ (μ : Measure X).support, ∀ f ∈ (μ : Measure X).support,
      ‖p e - p f‖ ≤ L * dist (z e) (z f) + b)
    {e : X} (he : e ∈ (μ : Measure X).support) :
    ‖p e - originalCountingVectorField base L z p μ (z e)‖ ≤ b := by
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro i
  have hi := originalCountingRoughField_node_bounds base L z (fun a ↦ p a i) μ hμ
    (b := b) (fun a ha d hd ↦ by
      have hr := hrough a ha d hd
      have hp := norm_le_pi_norm (p a - p d) i
      have hab := le_abs_self (p a i - p d i)
      simp only [Real.norm_eq_abs, Pi.sub_apply] at hp
      linarith) he
  change |p e i - originalCountingVectorField base L z p μ (z e) i| ≤ b
  change p e i - b ≤ originalCountingVectorField base L z p μ (z e) i ∧
    originalCountingVectorField base L z p μ (z e) i ≤ p e i at hi
  exact abs_le.mpr ⟨by linarith [hi.2], by linarith [hi.1]⟩

/-- Actual atom transport and the corresponding spatial isometry commute
with the vector field, independently of the original shell-code representation. -/
theorem originalCountingVectorField_mapHomeomorph
    (base : X) (L : ℝ≥0) (z : X → Y) (p : X → ι → ℝ) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) (T : X ≃ₜ X) (R : Y → Y) (hR : Isometry R)
    (hz : ∀ a, z (T a) = R (z a)) (hp : ∀ a, p (T a) = p a) (x : Y) :
    originalCountingVectorField base L z p (localFiniteMapHomeomorph T μ) (R x) =
      originalCountingVectorField base L z p μ x := by
  funext i
  exact originalCountingRoughField_mapHomeomorph base L z (fun e ↦ p e i) μ hμ T R hR hz
    (fun a ↦ congrFun (hp a) i) x

end OTSelector.Reconstruction

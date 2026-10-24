import OTSelector.Reconstruction.MarkedStationaryValueHaarRootBoundary
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Actual multidimensional Haar-root scene stationarity

The original environment can vary with the sample size. Only its independent
actual cube root is averaged. A genuine reroot cocycle and a weak scene limit
produce invariance of that limit; no stationarity of a finite environment or
finite optimizer is assumed.
-/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι Ω X : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace X]

/-- A scene law formed from its original environment and independent actual
normalized multidimensional Haar root. -/
def haarCubeAverageLaw (P : Measure Ω) (scene : Ω × (ι → ℝ) → X) (R : ℝ) : Measure X :=
  (P.prod (haarCubeRootLaw ι R)).map scene

theorem isProbabilityMeasure_haarCubeAverageLaw (P : Measure Ω) [IsProbabilityMeasure P]
    {scene : Ω × (ι → ℝ) → X} (hscene : Measurable scene) {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (haarCubeAverageLaw P scene R) := by
  let : IsProbabilityMeasure (haarCubeRootLaw ι R) := isProbabilityMeasure_haarCubeRootLaw ι hR
  exact Measure.isProbabilityMeasure_map hscene.aemeasurable

/-- Test integrals retain the actual original environment and its independent
root, including every additional fixed coefficient or chart tag. -/
theorem integral_haarCubeAverageLaw (P : Measure Ω) [IsProbabilityMeasure P]
    {scene : Ω × (ι → ℝ) → X} (hscene : Measurable scene) {R : ℝ} (hR : 0 < R)
    {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂haarCubeAverageLaw P scene R) =
      ∫ w, ∫ z, f (scene (w, z)) ∂haarCubeRootLaw ι R ∂P := by
  let : IsProbabilityMeasure (haarCubeRootLaw ι R) := isProbabilityMeasure_haarCubeRootLaw ι hR
  rw [haarCubeAverageLaw, integral_map hscene.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ ⟨(hf.comp hscene).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (.of_forall (fun p ↦ hbound (scene p)))⟩

/-- A genuine scene reroot has a boundary error supplied by the actual cube
root even when the original environment law and scene are arbitrary. -/
theorem norm_integral_haarCubeAverageLaw_reroot_sub_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    {scene : Ω × (ι → ℝ) → X} (hscene : Measurable scene)
    {shift : X → X} (hshift : Measurable shift) (v : ι → ℝ)
    (hcocycle : ∀ w z, shift (scene (w, z)) = scene (w, z + v))
    {R S : ℝ} (hR : 0 < R) (hS : 0 ≤ S) (hRS : S ≤ R)
    (hv : ∀ i, |v i| ≤ S) {f : X → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    ‖(∫ x, f (shift x) ∂haarCubeAverageLaw P scene R) -
        ∫ x, f x ∂haarCubeAverageLaw P scene R‖ ≤
      2 * C * (((2 * (R + S)) ^ Fintype.card ι -
        (2 * (R - S)) ^ Fintype.card ι) / (2 * R) ^ Fintype.card ι) := by
  let : IsProbabilityMeasure (haarCubeRootLaw ι R) := isProbabilityMeasure_haarCubeRootLaw ι hR
  have hi : Integrable (fun p ↦ f (scene p)) (P.prod (haarCubeRootLaw ι R)) :=
    ⟨(hf.comp hscene).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (.of_forall (fun p ↦ hbound (scene p)))⟩
  have his : Integrable (fun p ↦ f (shift (scene p))) (P.prod (haarCubeRootLaw ι R)) :=
    ⟨((hf.comp hshift).comp hscene).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (.of_forall (fun p ↦ hbound (shift (scene p))))⟩
  have hfirst := integral_haarCubeAverageLaw P hscene hR
    (f := fun x ↦ f (shift x)) (hf.comp hshift) (fun x ↦ hbound (shift x))
  rw [hfirst,
    integral_haarCubeAverageLaw P hscene hR hf hbound,
    ← integral_sub his.integral_prod_left hi.integral_prod_left]
  simp_rw [hcocycle]
  simpa using norm_integral_le_of_norm_le_const (μ := P)
    (.of_forall (fun w ↦ norm_integral_haarCubeRootLaw_shift_sub_le ι
      ((hf.comp hscene).comp measurable_prodMk_left)
      hC (fun z ↦ hbound (scene (w, z))) v hS hRS hv))

section WeakLimit
variable [TopologicalSpace X] [BorelSpace X] [HasOuterApproxClosed X]

/-- Every actual weak limit of these original Haar-rooted scenes is preserved
by each continuous physical reroot satisfying the actual observation cocycle. -/
theorem measurePreserving_of_haarCubeAverageLaw_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (scene : ∀ n, Ω n × (ι → ℝ) → X) (hscene : ∀ n, Measurable (scene n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hlarge : Tendsto R atTop atTop)
    (μ : ℕ → ProbabilityMeasure X) {ν : ProbabilityMeasure X}
    (hlaw : ∀ n, (μ n : Measure X) = haarCubeAverageLaw (P n) (scene n) (R n))
    (hlim : Tendsto μ atTop (𝓝 ν))
    {shift : X → X} (hshift : Continuous shift) (v : ι → ℝ)
    (hcocycle : ∀ n w z, shift (scene n (w, z)) = scene n (w, z + v)) :
    MeasurePreserving shift (ν : Measure X) (ν : Measure X) := by
  have hshiftlim := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hlim hshift
  have hsame : Tendsto (fun n ↦ (μ n).map hshift.measurable.aemeasurable)
      atTop (𝓝 ν) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    have hold := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim f
    have herr : Tendsto (fun n ↦
        (∫ x, f (shift x) ∂(μ n : Measure X)) - ∫ x, f x ∂(μ n : Measure X)) atTop (𝓝 0) := by
      have herror := (tendsto_haarCube_boundaryError (Fintype.card ι) ‖f‖ ‖v‖).comp hlarge
      apply squeeze_zero_norm' ?_ herror
      filter_upwards [hlarge.eventually (eventually_ge_atTop ‖v‖)] with n hn
      rw [hlaw n]
      apply norm_integral_haarCubeAverageLaw_reroot_sub_le (P n) (hscene n)
        hshift.measurable v (hcocycle n) (hR n) (norm_nonneg _) hn
        (fun i ↦ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
        f.continuous.measurable (norm_nonneg _) f.norm_coe_le_norm
    have hsum := herr.add hold
    simp only [zero_add, sub_add_cancel] at hsum
    simpa only [ProbabilityMeasure.toMeasure_map,
      integral_map hshift.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable] using hsum
  have heq := tendsto_nhds_unique hshiftlim hsame
  refine ⟨hshift.measurable, ?_⟩
  exact congrArg (fun p : ProbabilityMeasure X ↦ (p : Measure X)) heq
end WeakLimit
end OTSelector.Reconstruction

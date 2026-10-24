import OTSelector.Reconstruction.JacobiComplianceClock
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Changing the base point of the same compliance integral

The original inverse quadratic form is integrated in the original family time.
A local graph representation changes this primitive only by its value at the local
base point. Finite-measure power integrability is invariant under this translation.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator Interval ENNReal

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction
open OTSelector.Geometry

/-- Adding a fixed matrix or vector does not change a positive moment under a finite law. -/
theorem integrable_norm_rpow_add_const_iff
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → E}
    (hf : AEStronglyMeasurable f μ) (K : E) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x ↦ ‖f x + K‖ ^ r) μ ↔ Integrable (fun x ↦ ‖f x‖ ^ r) μ := by
  have hp0 : ENNReal.ofReal r ≠ 0 := by simp [hr]
  rw [← ENNReal.toReal_ofReal hr.le,
    integrable_norm_rpow_iff (hf.add_const K) hp0 ENNReal.ofReal_ne_top,
    integrable_norm_rpow_iff hf hp0 ENNReal.ofReal_ne_top]
  constructor
  · intro h
    have heq : ((fun x ↦ f x + K) - fun _ ↦ K) = f := by
      ext x
      simp only [Pi.sub_apply, add_sub_cancel_right]
    rw [← heq]
    exact h.sub (memLp_const K)
  · intro h
    exact h.add (memLp_const K)

/-- A continuous inverse quadratic form has a continuous primitive everywhere in the
open conditional interval, even if its finite endpoints are singular. -/
theorem continuousOn_compliancePrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : ℝ → E} {a b c : ℝ} (hK : ContinuousOn K (Ioo a b)) (hc : c ∈ Ioo a b) :
    ContinuousOn (fun t ↦ ∫ q in c..t, K q) (Ioo a b) := by
  intro t ht
  apply (show HasDerivAt (fun u ↦ ∫ q in c..u, K q) (K t) t from ?_).continuousAt.continuousWithinAt
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (hK.mono (ordConnected_Ioo.uIcc_subset hc ht)).intervalIntegrable (μ := volume)
  · exact hK.stronglyMeasurableAtFilter isOpen_Ioo t ht
  · exact (hK t ht).continuousAt (isOpen_Ioo.mem_nhds ht)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exact rebasing in the original time, using the actual graph-clock inverse-Hessian
formula on just the local integration segment. No global adapted chart is needed. -/
theorem compliancePrimitive_eq_add_graphPrimitive
    {K : ℝ → Matrix n n ℝ} {l h c d t a b : ℝ}
    {J C : ℝ → Matrix n n ℝ} {s v : ℝ → ℝ}
    (hK : ContinuousOn K (Ioo l h)) (hc : c ∈ Ioo l h)
    (hd : d ∈ Ioo l h) (ht : t ∈ Ioo l h)
    (hJ : DifferentiableOn ℝ J (Ioo a b)) (hC : ContinuousOn C (Ioo a b))
    (hdet : ∀ q ∈ Ioo a b, (J q).det ≠ 0)
    (hs : ∀ q ∈ uIcc d t, HasDerivAt s (v q) q)
    (hv : ContinuousOn v (uIcc d t)) (himage : MapsTo s (uIcc d t) (Ioo a b))
    (hkernel : ∀ q ∈ uIcc d t,
      K q = v q • ((J (s q))⁻¹ * C (s q) * (J (s q))⁻¹ᵀ)) :
    (∫ q in c..t, K q) = (∫ q in c..d, K q) +
      jacobiCompliancePrimitive J C (s d) (s t) := by
  have hcd := (hK.mono (ordConnected_Ioo.uIcc_subset hc hd)).intervalIntegrable (μ := volume)
  have hdt := (hK.mono (ordConnected_Ioo.uIcc_subset hd ht)).intervalIntegrable (μ := volume)
  rw [← intervalIntegral.integral_add_adjacent_intervals hcd hdt]
  congr 1
  calc
    (∫ q in d..t, K q) = jacobiCompliancePrimitive
        (fun q ↦ J (s q)) (fun q ↦ v q • C (s q)) d t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with q hq
      simpa only [Matrix.mul_smul, Matrix.smul_mul] using hkernel q (uIoc_subset_uIcc hq)
    _ = jacobiCompliancePrimitive J C (s d) (s t) :=
      jacobiCompliancePrimitive_graphClock hJ hC hdet hs hv himage

end OTSelector.Reconstruction

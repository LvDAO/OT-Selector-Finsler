import OTSelector.Reconstruction.CompliancePrimitiveRebasing
import OTSelector.Geometry.FocalConditionalMomentsPositive

/-!
# Regularity of the original kernel from actual local graph formulas

The original label Hessian inverse is the signed speed times the graph compliance
integrand. Positive actual clocks and the same positive graph Hessian supply its
positivity. Local formulas suffice for continuity throughout the open original
interval; a single manifold chart over the complete interval is unnecessary.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator

namespace OTSelector.Reconstruction
open OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An exact local graph expression yields continuity and positivity of the original
label kernel on that physical domain. The only speed sign is the actual graph clock. -/
theorem continuousOn_posSemidef_of_jacobiKernel
    {K J C : ℝ → Matrix n n ℝ} {s v : ℝ → ℝ} {I : Set ℝ} {a b : ℝ}
    (hJ : DifferentiableOn ℝ J (Ioo a b)) (hC : ContinuousOn C (Ioo a b))
    (hdet : ∀ q ∈ Ioo a b, (J q).det ≠ 0)
    (hCpos : ∀ q ∈ Ioo a b, (C q).PosSemidef)
    (hs : ContinuousOn s I) (hv : ContinuousOn v I) (hv0 : ∀ t ∈ I, 0 ≤ v t)
    (himage : MapsTo s I (Ioo a b))
    (hkernel : ∀ t ∈ I, K t = v t • ((J (s t))⁻¹ * C (s t) * (J (s t))⁻¹ᵀ)) :
    ContinuousOn K I ∧ ∀ t ∈ I, (K t).PosSemidef := by
  constructor
  · exact (hv.smul ((continuousOn_jacobiComplianceIntegrand hJ hC hdet).comp hs himage)).congr
      (fun t ht ↦ hkernel t ht)
  · intro t ht
    rw [hkernel t ht]
    apply Matrix.PosSemidef.smul _ (hv0 t ht)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hCpos _ (himage ht)).mul_mul_conjTranspose_same ((J (s t))⁻¹)

/-- One actual graph neighborhood at each interior time produces the global open
interval regularity of the same original kernel. No global frame choice is required. -/
theorem continuousOn_posSemidef_of_local_jacobiKernels
    {K : ℝ → Matrix n n ℝ} {a b : ℝ}
    (hlocal : ∀ t ∈ Ioo a b, ∃ (U : Set ℝ) (J C : ℝ → Matrix n n ℝ)
      (s v : ℝ → ℝ) (l h : ℝ), IsOpen U ∧ t ∈ U ∧
      DifferentiableOn ℝ J (Ioo l h) ∧ ContinuousOn C (Ioo l h) ∧
      (∀ q ∈ Ioo l h, (J q).det ≠ 0) ∧
      (∀ q ∈ Ioo l h, (C q).PosSemidef) ∧
      ContinuousOn s U ∧ ContinuousOn v U ∧ (∀ q ∈ U, 0 ≤ v q) ∧
      MapsTo s U (Ioo l h) ∧
      (∀ q ∈ U, K q = v q • ((J (s q))⁻¹ * C (s q) * (J (s q))⁻¹ᵀ))) :
    ContinuousOn K (Ioo a b) ∧ ∀ t ∈ Ioo a b, (K t).PosSemidef := by
  have hat : ∀ t ∈ Ioo a b, ContinuousAt K t ∧ (K t).PosSemidef := by
    intro t ht
    obtain ⟨U, J, C, s, v, l, h, hU, htU, hJ, hC, hd, hCp, hs, hv, hv0,
      hmap, hkernel⟩ := hlocal t ht
    obtain ⟨hcont, hpos⟩ := continuousOn_posSemidef_of_jacobiKernel
      hJ hC hd hCp hs hv hv0 hmap hkernel
    exact ⟨(hcont t htU).continuousAt (hU.mem_nhds htU), hpos t htU⟩
  exact ⟨fun t ht ↦ (hat t ht).1.continuousWithinAt, fun t ht ↦ (hat t ht).2⟩

end OTSelector.Reconstruction

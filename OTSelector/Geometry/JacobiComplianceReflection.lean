import OTSelector.MeasureTheory.Measure.ChangeOfDensity
import OTSelector.Geometry.JacobiPrimitive
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
Conditions: A measurable equivalence, an arbitrary measure and an extended nonnegative density.

Objects: The exact pushforward-withDensity identity using the inverse equivalence.

Proof detail: Test equality on measurable sets and change variables through the equivalence, retaining the actual density.

Sources: D. H. Fremlin, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf); D. H. Fremlin, Section 235G, integration along an inverse-measure-preserving map (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf).
Relation: Change-of-measure adapter, requiring no smoothness or Jacobi equation.
-/

/-!
# Changing the inward coordinate of an actual Jacobi conditional law

Reflection reverses the momentum and the signed compliance primitive while preserving
the Hamiltonian equations and the positive velocity coefficient. The same pushforward
of the original conditional measure retains its exact density formula. Translation
provides the analogous left-end coordinate change. All identities concern the actual
interval integral and original measure; no new population is introduced.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator ENNReal

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Reflection gives the negative original compliance integral based at the reflected root. -/
theorem jacobiCompliancePrimitive_reflect (J C : ℝ → Matrix n n ℝ) (b c s : ℝ) :
    jacobiCompliancePrimitive (fun t ↦ J (b - t)) (fun t ↦ C (b - t)) (b - c) s =
      -jacobiCompliancePrimitive J C c (b - s) := by
  unfold jacobiCompliancePrimitive
  rw [intervalIntegral.integral_comp_sub_left (fun t ↦ (J t)⁻¹ * C t * (J t)⁻¹ᵀ)]
  simp only [sub_sub_cancel]
  exact intervalIntegral.integral_symm _ _

/-- Translation of time preserves the actual compliance integral. -/
theorem jacobiCompliancePrimitive_translate (J C : ℝ → Matrix n n ℝ) (a c s : ℝ) :
    jacobiCompliancePrimitive (fun t ↦ J (a + t)) (fun t ↦ C (a + t)) (c - a) s =
      jacobiCompliancePrimitive J C c (a + s) := by
  unfold jacobiCompliancePrimitive
  rw [intervalIntegral.integral_comp_add_left (fun t ↦ (J t)⁻¹ * C t * (J t)⁻¹ᵀ)]
  congr 1
  ring

omit [DecidableEq n] in
/-- The reflected position and negated momentum solve the reflected Hamiltonian system. -/
theorem hamiltonian_system_reflect
    {J P A B C : ℝ → Matrix n n ℝ} {a b : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    {s : ℝ} (hs : s ∈ Ioo 0 (b - a)) :
    HasDerivAt (fun t ↦ J (b - t))
        ((-B (b - s)) * J (b - s) + C (b - s) * (-P (b - s))) s ∧
      HasDerivAt (fun t ↦ -P (b - t))
        (-A (b - s) * J (b - s) - (-B (b - s))ᵀ * (-P (b - s))) s := by
  have hs' : b - s ∈ Ioo a b := by constructor <;> linarith [hs.1, hs.2]
  have hinner := (hasDerivAt_id s).const_sub b
  constructor
  · convert! (hJ (b - s) hs').scomp s hinner using 1
    simp only [ neg_smul, one_smul, Matrix.neg_mul, Matrix.mul_neg,
        neg_add_rev]
    abel
  · convert! (hP (b - s) hs').neg.scomp s hinner using 1
    simp only [ neg_smul, one_smul, neg_neg, Matrix.transpose_neg,
        Matrix.neg_mul, Matrix.mul_neg]



/-- Reflection transports an interval density by the same involution and preserves its mass. -/
theorem map_reflect_interval_density (d : ℝ → ℝ≥0∞) (a b : ℝ) :
    ((volume.restrict (Ioo a b)).withDensity d).map (fun t ↦ b - t) =
      (volume.restrict (Ioo 0 (b - a))).withDensity (fun s ↦ d (b - s)) := by
  let e := MeasurableEquiv.subLeft b
  have hpre : (fun t : ℝ ↦ b - t) ⁻¹' Ioo 0 (b - a) = Ioo a b := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hbase : (volume.restrict (Ioo a b)).map (fun t ↦ b - t) =
      volume.restrict (Ioo 0 (b - a)) := by
    have h := ((volume : Measure ℝ).measurePreserving_sub_left b).restrict_preimage_emb
      (measurableEmbedding_subLeft b) (Ioo 0 (b - a))
    simpa only [hpre] using h.map_eq
  have h := map_withDensity_measurableEquiv e (volume.restrict (Ioo a b)) d
  change ((volume.restrict (Ioo a b)).withDensity d).map (fun t ↦ b - t) =
    ((volume.restrict (Ioo a b)).map (fun t ↦ b - t)).withDensity
      (fun s ↦ d (-s + b)) at h
  rw [hbase] at h
  simpa only [sub_eq_neg_add] using h

/-- Translation to the left-end inward coordinate transports the original interval density. -/
theorem map_translate_interval_density (d : ℝ → ℝ≥0∞) (a b : ℝ) :
    ((volume.restrict (Ioo a b)).withDensity d).map (fun t ↦ t - a) =
      (volume.restrict (Ioo 0 (b - a))).withDensity (fun s ↦ d (a + s)) := by
  let e := MeasurableEquiv.subRight a
  have hpre : (fun t : ℝ ↦ t - a) ⁻¹' Ioo 0 (b - a) = Ioo a b := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hbase : (volume.restrict (Ioo a b)).map (fun t ↦ t - a) =
      volume.restrict (Ioo 0 (b - a)) := by
    have h := (measurePreserving_add_right (volume : Measure ℝ) (-a)).restrict_preimage_emb
      (measurableEmbedding_subRight a) (Ioo 0 (b - a))
    simp only [← sub_eq_add_neg] at h
    simpa only [hpre] using h.map_eq
  have h := map_withDensity_measurableEquiv e (volume.restrict (Ioo a b)) d
  change ((volume.restrict (Ioo a b)).withDensity d).map (fun t ↦ t - a) =
    ((volume.restrict (Ioo a b)).map (fun t ↦ t - a)).withDensity
      (fun s ↦ d (s + a)) at h
  simpa only [hbase, add_comm] using h

/-- Local moment integrability of the reflected population is precisely integrability
on the original right-end interval. -/
theorem integrableOn_reflected_rpow_iff {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (μ : Measure ℝ) (b ε r : ℝ) :
    IntegrableOn (fun s ↦ ‖f (b - s)‖ ^ r) (Ioo 0 ε)
        (μ.map (fun t ↦ b - t)) ↔
      IntegrableOn (fun t ↦ ‖f t‖ ^ r) (Ioo (b - ε) b) μ := by
  rw [(measurableEmbedding_subLeft b).integrableOn_map_iff]
  have hpre : (fun t : ℝ ↦ b - t) ⁻¹' Ioo 0 ε = Ioo (b - ε) b := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [Function.comp_def, sub_sub_cancel, hpre]

omit [DecidableEq n] in
/-- Translating both position and momentum preserves the actual Hamiltonian system. -/
theorem hamiltonian_system_translate
    {J P A B C : ℝ → Matrix n n ℝ} {a b : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    {s : ℝ} (hs : s ∈ Ioo 0 (b - a)) :
    HasDerivAt (fun t ↦ J (a + t))
        (B (a + s) * J (a + s) + C (a + s) * P (a + s)) s ∧
      HasDerivAt (fun t ↦ P (a + t))
        (-A (a + s) * J (a + s) - (B (a + s))ᵀ * P (a + s)) s := by
  have hs' : a + s ∈ Ioo a b := by constructor <;> linarith [hs.1, hs.2]
  have hinner := (hasDerivAt_id s).const_add a
  constructor
  · simpa only [one_smul] using! (hJ (a + s) hs').scomp s hinner
  · simpa only [one_smul] using! (hP (a + s) hs').scomp s hinner

/-- Local moments after translation are precisely moments on the original left-end interval. -/
theorem integrableOn_translated_rpow_iff {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (μ : Measure ℝ) (a ε r : ℝ) :
    IntegrableOn (fun s ↦ ‖f (a + s)‖ ^ r) (Ioo 0 ε)
        (μ.map (fun t ↦ t - a)) ↔
      IntegrableOn (fun t ↦ ‖f t‖ ^ r) (Ioo a (a + ε)) μ := by
  rw [(measurableEmbedding_subRight a).integrableOn_map_iff]
  have hpre : (fun t : ℝ ↦ t - a) ⁻¹' Ioo 0 ε = Ioo a (a + ε) := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hshift (t : ℝ) : a + (t - a) = t := by ring
  simp only [Function.comp_def, hshift, hpre]

end OTSelector.Geometry

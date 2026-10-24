import OTSelector.Geometry.FocalConditionalPowerMoments
import OTSelector.Geometry.JacobiComplianceReflection

/-!
# Left-end power moments in the original time coordinate

Translation transports the actual Hamiltonian system, its true compliance integral,
and the same original conditional measure to the inward endpoint parameter.
-/

open Set MeasureTheory Matrix LinearMap
open scoped Topology Matrix.Norms.Operator ENNReal

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A regular left endpoint gives all local moments below its nullity plus one
for the original compliance primitive and original conditional measure. -/
theorem exists_integrableOn_jacobiCompliance_rpow_near_regular_left_endpoint
    {J P A B C : ℝ → Matrix n n ℝ} {a b c θ r : ℝ} {D : Matrix n n ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b))
    (hAsym : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hCsym : ∀ t ∈ Ioo a b, (C t)ᵀ = C t)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) (hc : c ∈ Ioo a b)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c)
    (hJa : HasDerivWithinAt J D (Ici a) a)
    (hcross : ∀ v, J a *ᵥ v = 0 →
      D *ᵥ v ∈ LinearMap.range (J a).mulVecLin → v = 0)
    {ρ w : ℝ → ℝ} {R : ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc a b))
    (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo a b, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo a b, 0 ≤ w t) (hθ : 0 < θ)
    {μ : Measure ℝ}
    (hμ : μ = (volume.restrict (Ioo a b)).withDensity
      (fun t ↦ ENNReal.ofReal ((ρ t * w t / θ) * |(J t).det|)))
    (hr0 : 0 < r) (hr : r < (Module.finrank ℝ (ker (J a).mulVecLin) : ℝ) + 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < b - a ∧
      IntegrableOn (fun t ↦ ‖jacobiCompliancePrimitive J C c t‖ ^ r) (Ioo a (a + ε)) μ := by
  have hmap : MapsTo (fun t : ℝ ↦ a + t) (Icc 0 (b - a)) (Icc a b) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hmapi : MapsTo (fun t : ℝ ↦ a + t) (Ioo 0 (b - a)) (Ioo a b) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hcomp : ContinuousOn (fun t : ℝ ↦ a + t) (Icc 0 (b - a)) := by fun_prop
  have hcnew : c - a ∈ Ioo 0 (b - a) := by
    constructor <;> linarith [hc.1, hc.2]
  have hcenter : a + (c - a) = c := by ring
  have hinitnew : (J (a + (c - a)))ᵀ * P (a + (c - a)) =
      (P (a + (c - a)))ᵀ * J (a + (c - a)) := by
    simpa only [hcenter] using hinit
  have hcrossnew : ∀ v, J (a + 0) *ᵥ v = 0 →
      D *ᵥ v ∈ LinearMap.range (J (a + 0)).mulVecLin → v = 0 := by
    simpa only [add_zero] using hcross
  have hμnew : μ.map (fun t ↦ t - a) =
      (volume.restrict (Ioo 0 (b - a))).withDensity (fun s ↦
        ENNReal.ofReal (((ρ (a + s)) * (w (a + s)) / θ) * |(J (a + s)).det|)) := by
    rw [hμ, map_translate_interval_density]
  have hrnew : r < (Module.finrank ℝ (ker (J (a + 0)).mulVecLin) : ℝ) + 1 := by
    rw [add_zero]
    exact hr
  obtain ⟨ε, hε, hεab, hmoment⟩ :=
    exists_integrableOn_jacobiCompliance_rpow_near_regular_endpoint
      (fun s hs ↦ (hamiltonian_system_translate hJ hP hs).1)
      (fun s hs ↦ (hamiltonian_system_translate hJ hP hs).2)
      (hA.comp hcomp hmap) (hB.comp hcomp hmap) (hC.comp hcomp hmap)
      (fun s hs ↦ hAsym _ (hmapi hs)) (fun s hs ↦ hCsym _ (hmapi hs))
      (fun s hs ↦ hd _ (hmapi hs)) hcnew hinitnew
      (hasDerivWithinAt_left_inward_parameter hJa) hcrossnew
      (hρ.comp (measurable_const.add measurable_id)) (hw.comp hcomp hmap)
      (fun s hs ↦ hρ0 _ (hmapi hs)) (fun s hs ↦ hρR _ (hmapi hs))
      (fun s hs ↦ hw0 _ (hmapi hs)) hθ hμnew hr0 hrnew
  refine ⟨ε, hε, hεab, ?_⟩
  apply (integrableOn_translated_rpow_iff (jacobiCompliancePrimitive J C c) μ a ε r).1
  simpa only [jacobiCompliancePrimitive_translate] using hmoment

end OTSelector.Geometry

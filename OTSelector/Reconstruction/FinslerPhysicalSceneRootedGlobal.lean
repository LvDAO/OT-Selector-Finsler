import OTSelector.Reconstruction.FinslerPhysicalSceneClockEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedLaw

/-!
# Actual global allocation families as finite physical scene inputs

Jointly measurable original allocation coefficients and targets construct the
physical plan family.  Its finite completion changes only the null event where
the actual allocation fails to be feasible.  Both the original compact carriers
and every nonnegative physical energy integral are retained almost surely.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped ENNReal

noncomputable section
namespace OTSelector.Reconstruction

section FiniteVersion

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- Set a physical plan to zero only on its nonfinite exceptional event. -/
def physicalSceneFinitePlanVersion (Γ : Ω → Measure X) (w : Ω) : Measure X :=
  if Γ w univ < ⊤ then Γ w else 0

instance (Γ : Ω → Measure X) (w : Ω) :
    IsFiniteMeasure (physicalSceneFinitePlanVersion Γ w) := by
  unfold physicalSceneFinitePlanVersion
  split_ifs with h
  · exact ⟨h⟩
  · infer_instance

/-- The actual finite completion is Giry-measurable. -/
theorem measurable_physicalSceneFinitePlanVersion
    (Γ : Ω → Measure X) (hΓ : Measurable Γ) :
    Measurable (physicalSceneFinitePlanVersion Γ) :=
  Measurable.ite
    (measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp hΓ) measurable_const)
    hΓ measurable_const

/-- Almost-sure finiteness makes this the same original plan almost everywhere. -/
theorem physicalSceneFinitePlanVersion_ae_eq
    (P : Measure Ω) (Γ : Ω → Measure X)
    (hfinite : ∀ᵐ w ∂P, IsFiniteMeasure (Γ w)) :
    physicalSceneFinitePlanVersion Γ =ᵐ[P] Γ := by
  filter_upwards [hfinite] with w hw
  simp only [physicalSceneFinitePlanVersion, ite_eq_left (measure_lt_top (Γ w) univ)]

end FiniteVersion

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M] {n : ℕ}

/-- Original measurable coefficients and physical targets give a measurable
physical plan family on the unchanged global source law. -/
theorem measurable_physicalSceneAllocationPlan
    (μ : Measure M) [SFinite μ]
    (a : Ω → M → Fin (n + 1) → ℝ)
    (ha : ∀ j, Measurable (fun z : Ω × M ↦ a z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j)) :
    Measurable (fun w ↦ physicalSceneAllocationPlan μ (a w) (Y w)) :=
  measurable_parameterizedSemidiscretePlan μ (fun z : Ω × M ↦ a z.1 z.2) ha
    Prod.snd measurable_snd Y hY

/-- The actual sampled physical allocation plan, finite at every environment
after changing only the nonfinite exceptional event. -/
def physicalSceneGlobalAllocationFamily
    (μ : Measure M) (a : Ω → M → Fin (n + 1) → ℝ)
    (Y : Ω → Fin (n + 1) → M) : Ω → Measure (M × M) :=
  physicalSceneFinitePlanVersion (fun w ↦ physicalSceneAllocationPlan μ (a w) (Y w))

instance (μ : Measure M) (a : Ω → M → Fin (n + 1) → ℝ)
    (Y : Ω → Fin (n + 1) → M) (w : Ω) :
    IsFiniteMeasure (physicalSceneGlobalAllocationFamily μ a Y w) :=
  inferInstanceAs (IsFiniteMeasure (physicalSceneFinitePlanVersion _ w))

/-- The actual finite global family is measurable from its original inputs. -/
theorem measurable_physicalSceneGlobalAllocationFamily
    (μ : Measure M) [SFinite μ]
    (a : Ω → M → Fin (n + 1) → ℝ)
    (ha : ∀ j, Measurable (fun z : Ω × M ↦ a z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j)) :
    Measurable (physicalSceneGlobalAllocationFamily μ a Y) :=
  measurable_physicalSceneFinitePlanVersion _
    (measurable_physicalSceneAllocationPlan μ a ha Y hY)

/-- Almost-sure original feasibility retains the same actual physical plans. -/
theorem physicalSceneGlobalAllocationFamily_ae_eq
    (P : Measure Ω) (μ : Measure M) [IsFiniteMeasure μ]
    (a : Ω → M → Fin (n + 1) → ℝ) (Y : Ω → Fin (n + 1) → M)
    (p : Ω → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (a w)) :
    physicalSceneGlobalAllocationFamily μ a Y =ᵐ[P]
      fun w ↦ physicalSceneAllocationPlan μ (a w) (Y w) :=
  physicalSceneFinitePlanVersion_ae_eq P _
    (hfeas.mono fun w hw ↦ finite_physicalSceneAllocationPlan hw (Y w))

/-- The original physical source and sampled target carriers pass to the
actual finite family on the same probability-one event. -/
theorem ae_physicalSceneGlobalAllocationFamily_carried
    (P : Measure Ω) (μ : Measure M) [IsFiniteMeasure μ]
    (a : Ω → M → Fin (n + 1) → ℝ) (Y : Ω → Fin (n + 1) → M)
    (p : Ω → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (a w))
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hYB : ∀ᵐ w ∂P, ∀ j, Y w j ∈ B) :
    ∀ᵐ w ∂P, ∀ᵐ e ∂physicalSceneGlobalAllocationFamily μ a Y w,
      e.1 ∈ A ∧ e.2 ∈ B := by
  filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq P μ a Y p hfeas,
    hfeas, hYB] with w heq hw htarget
  rw [heq]
  exact ae_physicalSceneAllocationPlan_carried hw (Y w) hA hB hμA htarget

/-- Every nonnegative original physical energy is exactly the original
allocation energy in the unchanged random environment. -/
theorem lintegral_physicalSceneGlobalAllocationFamily_eq
    (P : Measure Ω) (μ : Measure M) [IsFiniteMeasure μ]
    (a : Ω → M → Fin (n + 1) → ℝ) (Y : Ω → Fin (n + 1) → M)
    (p : Ω → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (a w))
    (energy : Ω → M × M → ℝ≥0∞) (henergy : ∀ w, Measurable (energy w)) :
    (∫⁻ w, ∫⁻ e, energy w e ∂physicalSceneGlobalAllocationFamily μ a Y w ∂P) =
      ∫⁻ w, ∫⁻ e, energy w (e.1, Y w e.2) ∂semidiscreteAllocationMeasure μ (a w) ∂P := by
  apply lintegral_congr_ae
  filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq P μ a Y p hfeas] with w heq
  rw [heq]
  exact lintegral_physicalSceneAllocationPlan μ (a w) (Y w) (energy w) (henergy w)

end OTSelector.Reconstruction

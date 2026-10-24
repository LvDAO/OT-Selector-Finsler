import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindow
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootBoundary

/-!
# Jointly measurable physical windows of the same original rooted inputs

The root is added as an unchanged tag to each used original observation.
Restriction is then one fixed measurable prefix operation. This proves joint
measurability without a law for an unused tail, and exact fixed-root laws retain
both original colors and their original scalar populations.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Root-dependent physical placement of the same original point, with its
original scalar clock retained. -/
def legalInputRootPoint (q : ℕ) (side : ℝ≥0)
    (p : (Fin q → ℝ) × ((Fin q → ℝ) × ℝ)) : (Fin q → ℝ) × ℝ :=
  (legalInputPhysicalPoint q (fun i ↦ -(side : ℝ) / 2 - p.1 i) side p.2.1, p.2.2)

theorem measurable_legalInputRootPoint (q : ℕ) (side : ℝ≥0) :
    Measurable (legalInputRootPoint q side) := by
  unfold legalInputRootPoint legalInputPhysicalPoint
  fun_prop

/-- Keep the literal original count and repeat only the same independent Haar
root as a tag, leaving every original used point unchanged. -/
def legalInputTaggedOriginalCloud (q : ℕ)
    (p : (Fin q → ℝ) × MarkedCloudSpace q ℝ) :
    ℕ × (ℕ → ((Fin q → ℝ) × ((Fin q → ℝ) × ℝ))) :=
  (p.2.1, fun i ↦ (p.1, p.2.2 i))

theorem measurable_legalInputTaggedOriginalCloud (q : ℕ) :
    Measurable (legalInputTaggedOriginalCloud q) := by
  apply measurable_snd.fst.prodMk
  apply measurable_pi_lambda
  intro i
  exact measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd.snd)

/-- Actual used points in a physical root window. The membership predicate
is fixed on root-tagged original points, so no adaptive input law is needed. -/
def legalInputRootWindowPrefix (q : ℕ) (side : ℝ≥0) (U : Set (Fin q → ℝ))
    (p : (Fin q → ℝ) × MarkedCloudSpace q ℝ) : BlockData ((Fin q → ℝ) × ℝ) :=
  mapBlockData (legalInputRootPoint q side)
    (restrictedPrefix ((legalInputRootPoint q side) ⁻¹' (Prod.fst ⁻¹' U))
      (legalInputTaggedOriginalCloud q p))

theorem measurable_legalInputRootWindowPrefix (q : ℕ) (side : ℝ≥0)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U) :
    Measurable (legalInputRootWindowPrefix q side U) :=
  (measurable_mapBlockData (measurable_legalInputRootPoint q side)).comp
    ((measurable_restrictedPrefix ((hU.preimage measurable_fst).preimage
      (measurable_legalInputRootPoint q side))).comp (measurable_legalInputTaggedOriginalCloud q))

/-- The jointly measurable construction is exactly the same original finite
prefix as restriction at any fixed original Haar root. -/
theorem legalInputRootWindowPrefix_eq (q : ℕ) (side : ℝ≥0) (U : Set (Fin q → ℝ))
    (z : Fin q → ℝ) (ω : MarkedCloudSpace q ℝ) :
    legalInputRootWindowPrefix q side U (z, ω) =
      legalInputWindowPrefix q (fun i ↦ -(side : ℝ) / 2 - z i) side U ω := by
  rw [legalInputRootWindowPrefix, mapBlockData_restrictedPrefix]
  change restrictedPrefix (Prod.fst ⁻¹' U)
    (ω.1, fun i ↦ legalInputRootPoint q side (z, ω.2 i)) = _
  change _ = mapBlockData
    (Prod.map (legalInputPhysicalPoint q (fun i ↦ -(side : ℝ) / 2 - z i) side) id)
    (restrictedPrefix ((Prod.map
      (legalInputPhysicalPoint q (fun i ↦ -(side : ℝ) / 2 - z i) side) id) ⁻¹' (Prod.fst ⁻¹' U)) ω)
  rw [mapBlockData_restrictedPrefix]
  rfl

/-- The same original Haar root is shared by both original independent colors. -/
def legalInputRootWindows (q : ℕ) (side : ℝ≥0) (U : Set (Fin q → ℝ))
    (p : (Fin q → ℝ) × TwoMarkedCloudSpace q ℝ ℝ) :
    BlockData ((Fin q → ℝ) × ℝ) × BlockData ((Fin q → ℝ) × ℝ) :=
  (legalInputRootWindowPrefix q side U (p.1, p.2.1),
    legalInputRootWindowPrefix q side U (p.1, p.2.2))

theorem measurable_legalInputRootWindows (q : ℕ) (side : ℝ≥0)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U) :
    Measurable (legalInputRootWindows q side U) :=
  ((measurable_legalInputRootWindowPrefix q side hU).comp
    (measurable_fst.prodMk measurable_snd.fst)).prodMk
    ((measurable_legalInputRootWindowPrefix q side hU).comp
      (measurable_fst.prodMk measurable_snd.snd))

/-- At each interior actual root, the physical window has exactly the original
independent two-color Poisson law at its own physical volume. -/
theorem map_legalInputRootWindows_twoMarkedCloudLaw (q : ℕ)
    {side : ℝ≥0} (hside : 0 < side) (z : Fin q → ℝ)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ legalInputPhysicalBox q (fun i ↦ -(side : ℝ) / 2 - z i) side)
    (hpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    let _window := isProbabilityMeasure_legalInputWindowLaw q _ hside hU hsub hpos
    (twoMarkedCloudLaw q ℝ ℝ α β (side ^ q)).map (fun ω ↦ legalInputRootWindows q side U (z, ω)) =
      (blockDataLaw ((normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)).prod α)
        (fun n ↦ poissonMeasure (volume U).toNNReal {n})).prod
      (blockDataLaw ((normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)).prod β)
        (fun n ↦ poissonMeasure (volume U).toNNReal {n})) := by
  dsimp only
  have heq : (fun ω ↦ legalInputRootWindows q side U (z, ω)) =
      Prod.map (legalInputWindowPrefix q (fun i ↦ -(side : ℝ) / 2 - z i) side U)
        (legalInputWindowPrefix q (fun i ↦ -(side : ℝ) / 2 - z i) side U) := by
    funext ω
    exact Prod.ext (legalInputRootWindowPrefix_eq q side U z ω.1)
      (legalInputRootWindowPrefix_eq q side U z ω.2)
  rw [heq]
  exact map_legalInputWindowPrefix_twoMarkedCloudLaw q _ hside hU hsub hpos α β

end OTSelector.Reconstruction

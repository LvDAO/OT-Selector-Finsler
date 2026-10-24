import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineShape

/-! Distinguish original physical cost scale from the actual local point-count
intensity. Density changes the frozen kernel, not the original point count. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Exact cancellation of the positive original density in a homogeneous
cost at its actual point-count intensity; zero ambient intensity is included. -/
theorem rpow_positive_density_cancel {r density p : ℝ}
    (hr : 0 ≤ r) (hdensity : 0 < density) :
    (r * density) ^ p * density ^ (-p) = r ^ p := by
  rw [Real.mul_rpow hr hdensity.le, mul_assoc, ← Real.rpow_add hdensity,
    add_neg_cancel, Real.rpow_zero, mul_one]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Keeping the actual density in the count intensity requires its inverse
power in the kinetic kernel. The probe and the same allowed graph are kept. -/
theorem unclampedBlockLegalTilted_density (q : ℕ)
    (source : A → ℝ) (target : B → ℝ) {r density : ℝ}
    (hr : 0 ≤ r) (hdensity : 0 < density)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) :
    unclampedBlockLegalTilted q source target r kin probe t dS dT =
      unclampedBlockLegalTilted q source target (r * density)
        (fun a b v ↦ density ^ (-(2 / (q : ℝ))) * kin a b v) probe t dS dT := by
  unfold unclampedBlockLegalTilted
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j _
  rw [← mul_assoc, rpow_positive_density_cancel hr hdensity]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Actual affine physical quadratic costs agree with the density-scaled
legal model at its actual count intensity r*density*side^q. -/
theorem unclampedBlockLegalTilted_affine_density (q : ℕ) (hq : 0 < q)
    (source : A → ℝ) (target : B → ℝ) {r density side : ℝ}
    (hr : 0 ≤ r) (hdensity : 0 < density) (hside : 0 ≤ side) (origin : Fin q → ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    (probe : A → B → ℝ) (t : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B))
    (hS : ∀ i, (dS.2 i).1 ∈ unitCube q) (hT : ∀ j, (dT.2 j).1 ∈ unitCube q) :
    unclampedBlockLegalTilted q source target r kin probe t
      (mapBlockData (affineMarkedPoint origin side) dS)
      (mapBlockData (affineMarkedPoint origin side) dT) =
      blockLegalTilted q source target (r * density * side ^ q)
        (fun a b v ↦ density ^ (-(2 / (q : ℝ))) * kin a b v) probe t dS dT := by
  rw [unclampedBlockLegalTilted_affine q hq source target hr hside origin kin hhom probe t]
  rw [unclampedBlockLegalTilted_density q source target
    (mul_nonneg hr (pow_nonneg hside q)) hdensity kin probe t]
  have heq : r * side ^ q * density = r * density * side ^ q := by ring
  rw [heq]
  exact unclampedBlockLegalTilted_eq_block q source target _ _ probe t dS dT hS hT

/-- The identity holds on the exact original two-color shape laws, with no
law imposed on discarded endpoints or any artificial unused iid tail. -/
theorem ae_unclampedBlockLegalTilted_affine_density (q : ℕ) (hq : 0 < q)
    (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (countIntensity : ℝ≥0) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    {r density side : ℝ} (hr : 0 ≤ r) (hdensity : 0 < density) (hside : 0 ≤ side)
    (origin : Fin q → ℝ) (kin : A → B → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    (probe : A → B → ℝ) (t : ℝ) :
    ∀ᵐ d ∂(shapeBlockLaw q α countIntensity S).prod (shapeBlockLaw q β countIntensity S),
      unclampedBlockLegalTilted q source target r kin probe t
        (mapBlockData (affineMarkedPoint origin side) d.1)
        (mapBlockData (affineMarkedPoint origin side) d.2) =
      blockLegalTilted q source target (r * density * side ^ q)
        (fun a b v ↦ density ^ (-(2 / (q : ℝ))) * kin a b v) probe t d.1 d.2 := by
  filter_upwards [ae_shapeBlockLaw_unitCube_two q α β countIntensity hS] with d hd
  exact unclampedBlockLegalTilted_affine_density q hq source target hr hdensity hside origin
    kin hhom probe t d.1 d.2 hd.1 hd.2

/-- Expected true affine physical cost at the actual local count intensity.
The positive original density is kept in that intensity and canceled only in
the kinetic kernel; the original probe and shape error remain literal. -/
theorem FiniteScalarBins.integrable_density_affine_shapeBlockValue_compare
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) (hq : 0 < q) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r density side : ℝ≥0) (hdensity : 0 < density) (origin : Fin q → ℝ) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, source a < target b → |g a b| ≤ G) (t : ℝ) :
    let countIntensity := r * density * side ^ q
    let scaledKin := fun a b v ↦ (density : ℝ) ^ (-(2 / (q : ℝ))) * kin a b v
    let law := (shapeBlockLaw q α countIntensity S).prod (shapeBlockLaw q β countIntensity S)
    let value := fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      unclampedBlockLegalTilted q source target r kin g t
        (mapBlockData (affineMarkedPoint origin side) d.1)
        (mapBlockData (affineMarkedPoint origin side) d.2)
    Integrable value law ∧
    |(∫ d, value d ∂law) - legalMarkedPressure q source target α β countIntensity scaledKin g t| ≤
      (2 * (countIntensity : ℝ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) *
          ((countIntensity : ℝ) ^ (2 / (q : ℝ)) *
            (((density : ℝ) ^ (-(2 / (q : ℝ))) * C) * q) + |t| * G)) := by
  dsimp only
  let countIntensity := r * density * side ^ q
  let c := (density : ℝ) ^ (-(2 / (q : ℝ)))
  let scaledKin := fun a b v ↦ c * kin a b v
  have hc : 0 ≤ c := Real.rpow_nonneg density.coe_nonneg _
  have hm : Measurable (Function.uncurry (fun p : A × B ↦ scaledKin p.1 p.2)) :=
    measurable_const.mul hk
  have hb : ∀ a b, source a < target b → ∀ v,
      |scaledKin a b v| ≤ (c * C) * ∑ l, v l ^ 2 := by
    intro a b hab v
    calc
      _ = c * |kin a b v| := by
        change |c * kin a b v| = c * |kin a b v|
        rw [abs_mul, abs_of_nonneg hc]
      _ ≤ c * (C * ∑ l, v l ^ 2) := mul_le_mul_of_nonneg_left (hkb a b hab v) hc
      _ = _ := by ring
  obtain ⟨hInt, hbound⟩ := D.integrable_shapeBlockValue_compare_legalPressure hgap q hs ht
    α β countIntensity hS hsource hsep (mul_nonneg hc hC) hG hm hb hg hgb t
  have heq := ae_unclampedBlockLegalTilted_affine_density q hq source target α β
    countIntensity hS r.coe_nonneg (by exact_mod_cast hdensity) side.coe_nonneg origin kin hhom g t
  have heq' : (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      unclampedBlockLegalTilted q source target r kin g t
        (mapBlockData (affineMarkedPoint origin side) d.1)
        (mapBlockData (affineMarkedPoint origin side) d.2)) =ᵐ[
        (shapeBlockLaw q α countIntensity S).prod (shapeBlockLaw q β countIntensity S)]
      fun d ↦ blockLegalTilted q source target countIntensity scaledKin g t d.1 d.2 := by
    filter_upwards [heq] with d hd
    convert hd using 1 <;> simp only [countIntensity, NNReal.coe_mul, NNReal.coe_pow, scaledKin, c] <;> rfl
  refine ⟨hInt.congr heq'.symm, ?_⟩
  rw [integral_congr_ae heq']
  exact hbound

end OTSelector.Reconstruction

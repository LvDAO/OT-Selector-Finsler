import OTSelector.Reconstruction.MarkedStationaryValueLegalShape

/-! The measurable-shape error is paid by original spatial hole mass at the
finite cube scale, before any multiscale limit is taken. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Fill/delete comparison for the actual restriction of the original
homogeneous Poisson cloud to any measurable spatial shape. -/
theorem FiniteScalarBins.integral_shapeLegalMarkedTilted_sub_le
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (shapeLegalMarkedTilted q source target S r kin g t)
      (twoMarkedCloudLaw q A B α β r) ∧
    |(∫ ω, shapeLegalMarkedTilted q source target S r kin g t ω
        ∂twoMarkedCloudLaw q A B α β r) - legalMarkedPressure q source target α β r kin g t| ≤
      (2 * (r : ℝ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) *
          ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G)) := by
  let _instA : Nonempty A := nonempty_of_isProbabilityMeasure α
  let _instB : Nonempty B := nonempty_of_isProbabilityMeasure β
  let P := twoMarkedCloudLaw q A B α β r
  let V := shapeLegalMarkedTilted q source target S r kin g t
  let W := legalMarkedTilted q source target r kin g t
  let K := 2 * ((D.count : ℝ) + 1) *
    ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G)
  let missing : TwoMarkedCloudSpace q A B → ℝ := fun ω ↦
    (((mSourceCount ω - (shapeCloud S ω.1).1) +
      (mTargetCount ω - (shapeCloud S ω.2).1) : ℕ) : ℝ)
  have hsourceI := (integrable_shapeCloud_missing_count α r hS).comp_fst
    (markedPoissonLaw q B β r)
  have htargetI := (integrable_shapeCloud_missing_count β r hS).comp_snd
    (markedPoissonLaw q A α r)
  have hmissingI : Integrable missing P := by
    have hsum := hsourceI.add htargetI
    apply hsum.congr
    filter_upwards [] with ω
    simp only [missing, Nat.cast_add, mSourceCount, mTargetCount, Pi.add_apply]
  have hboundI := hmissingI.mul_const K
  have hfullI : Integrable W P := integrable_legalMarkedTilted q hs ht α β r
    hC hG hk hkb hg hgb t
  have hAE : ∀ᵐ ω ∂P, |V ω - W ω| ≤ missing ω * K := by
    filter_upwards [ae_all_mSourceMark q α β r hsource, ae_all_mMarkPair q α β r (P := fun a b ↦ gap ≤ |target b - source a|) hsep]
      with ω hsrc hpair
    exact D.abs_shapeLegalMarkedTilted_sub_le hgap q source target S r.coe_nonneg hC hG
      kin g t hkb hgb ω hsrc hpair
  have hmeas : Measurable V := measurable_shapeLegalMarkedTilted q hs ht hS r hk hg t
  have hshapeI : Integrable V P := (hfullI.norm.add hboundI).mono'
      hmeas.aestronglyMeasurable (by
    filter_upwards [hAE] with ω hω
    simp only [Pi.add_apply, Real.norm_eq_abs]
    apply abs_le.mpr
    have hlow := (abs_le.mp hω).1
    have hupp := (abs_le.mp hω).2
    have hpos := le_abs_self (W ω)
    have hneg := neg_abs_le (W ω)
    constructor <;> linarith)
  have hmeanSource :
      (∫ ω : TwoMarkedCloudSpace q A B, ((mSourceCount ω - (shapeCloud S ω.1).1 : ℕ) : ℝ) ∂P) =
        (r : ℝ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal := by
    change (∫ ω, ((ω.1.1 - (shapeCloud S ω.1).1 : ℕ) : ℝ)
      ∂(markedPoissonLaw q A α r).prod (markedPoissonLaw q B β r)) = _
    rw [integral_fun_fst (fun z : MarkedCloudSpace q A ↦ ((z.1 - (shapeCloud S z).1 : ℕ) : ℝ))]
    simpa using integral_shapeCloud_missing_count α r hS
  have hmeanTarget :
      (∫ ω : TwoMarkedCloudSpace q A B, ((mTargetCount ω - (shapeCloud S ω.2).1 : ℕ) : ℝ) ∂P) =
        (r : ℝ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal := by
    change (∫ ω, ((ω.2.1 - (shapeCloud S ω.2).1 : ℕ) : ℝ)
      ∂(markedPoissonLaw q A α r).prod (markedPoissonLaw q B β r)) = _
    rw [integral_fun_snd (fun z : MarkedCloudSpace q B ↦ ((z.1 - (shapeCloud S z).1 : ℕ) : ℝ))]
    simpa using integral_shapeCloud_missing_count β r hS
  have hmean : (∫ ω, missing ω ∂P) =
      2 * (r : ℝ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal := by
    simp only [missing, Nat.cast_add]
    have hadd := integral_add hsourceI htargetI
    change (∫ ω, ((ω.1.1 - (shapeCloud S ω.1).1 : ℕ) : ℝ) +
      ((ω.2.1 - (shapeCloud S ω.2).1 : ℕ) : ℝ)
      ∂(markedPoissonLaw q A α r).prod (markedPoissonLaw q B β r)) = _
    rw [hadd]
    change (∫ ω : TwoMarkedCloudSpace q A B, ((mSourceCount ω - (shapeCloud S ω.1).1 : ℕ) : ℝ) ∂P) +
      (∫ ω : TwoMarkedCloudSpace q A B, ((mTargetCount ω - (shapeCloud S ω.2).1 : ℕ) : ℝ) ∂P) = _
    rw [hmeanSource, hmeanTarget]
    ring
  refine ⟨hshapeI, ?_⟩
  change |(∫ ω, V ω ∂P) - ∫ ω, W ω ∂P| ≤ _
  calc
    _ = |∫ ω, V ω - W ω ∂P| := by rw [integral_sub hshapeI hfullI]
    _ ≤ ∫ ω, |V ω - W ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, missing ω * K ∂P :=
      integral_mono_ae (hshapeI.sub hfullI).abs hboundI hAE
    _ = _ := by rw [integral_mul_const, hmean]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Zero extension changes no edge in a literal finite legal block. -/
theorem blockLegalTilted_forward (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) :
    blockLegalTilted q source target r (forwardKinetic q source target kin)
      (forwardProbe source target g) t dS dT =
      blockLegalTilted q source target r kin g t dS dT := by
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j hij
  have hforward : source (dS.2 i).2 < target (dT.2 j).2 := by
    simpa only [scalarClockLegalGraph, Finset.mem_filter, Finset.mem_univ, true_and] using hij
  simp only [forwardKinetic, forwardProbe, hforward, ↓reduceIte]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- The literal shape restriction also ignores zero extension off legal pairs. -/
theorem shapeLegalMarkedTilted_forward (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (S : Set (Fin q → ℝ)) (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ)
    (g : A → B → ℝ) (t : ℝ) (ω : TwoMarkedCloudSpace q A B) :
    shapeLegalMarkedTilted q source target S r (forwardKinetic q source target kin)
      (forwardProbe source target g) t ω =
      shapeLegalMarkedTilted q source target S r kin g t ω :=
  blockLegalTilted_forward q source target r kin g t (shapeCloud S ω.1) (shapeCloud S ω.2)

/-- Arbitrary measurable holes in the spatial cube cost their original expected
point count, assuming kernel bounds only on original forward clock pairs. -/
theorem FiniteScalarBins.integral_shapeLegalMarkedTilted_sub_le_of_forward
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, source a < target b → |g a b| ≤ G) (t : ℝ) :
    Integrable (shapeLegalMarkedTilted q source target S r kin g t)
      (twoMarkedCloudLaw q A B α β r) ∧
    |(∫ ω, shapeLegalMarkedTilted q source target S r kin g t ω
        ∂twoMarkedCloudLaw q A B α β r) - legalMarkedPressure q source target α β r kin g t| ≤
      (2 * (r : ℝ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) *
          ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G)) := by
  have h := D.integral_shapeLegalMarkedTilted_sub_le hgap q hs ht α β r hS hsource hsep
    hC hG (measurable_forwardKinetic q hs ht hk) (abs_forwardKinetic_le q _ _ hC hkb)
    (measurable_forwardProbe hs ht hg) (abs_forwardProbe_le _ _ hG hgb) t
  have hshape : shapeLegalMarkedTilted q source target S r
      (forwardKinetic q source target kin) (forwardProbe source target g) t =
        shapeLegalMarkedTilted q source target S r kin g t :=
    funext (shapeLegalMarkedTilted_forward q source target S r kin g t)
  have hfull : legalMarkedPressure q source target α β r
      (forwardKinetic q source target kin) (forwardProbe source target g) t =
        legalMarkedPressure q source target α β r kin g t := by
    unfold legalMarkedPressure
    exact integral_congr_ae (.of_forall (legalMarkedTilted_forward q source target r kin g t))
  simpa only [hshape, hfull] using h

/-- At a fixed cube scale the per-intensity error is proportional to the original
spatial hole mass, with no regularity imposed on the shape. -/
theorem FiniteScalarBins.abs_normalized_shapeLegalMarkedTilted_sub_le
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (hr : 0 < (r : ℝ)) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, source a < target b → |g a b| ≤ G) (t : ℝ) :
    |(∫ ω, shapeLegalMarkedTilted q source target S r kin g t ω
        ∂twoMarkedCloudLaw q A B α β r) / (r : ℝ) -
      legalMarkedPressure q source target α β r kin g t / (r : ℝ)| ≤
      (2 * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) *
          ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G)) := by
  have h := (D.integral_shapeLegalMarkedTilted_sub_le_of_forward hgap q hs ht α β r hS
    hsource hsep hC hG hk hkb hg hgb t).2
  rw [← sub_div, abs_div, abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  calc
    _ ≤ (2 * (r : ℝ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) *
          ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G)) := h
    _ = _ := by ring

/-- Choose the hole tolerance after fixing the microscopic cube scale and before
choosing a measurable shape. This is uniform over all such shapes. -/
theorem FiniteScalarBins.exists_uniform_shape_hole_tolerance
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (hr : 0 < (r : ℝ))
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, source a < target b → |g a b| ≤ G) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Set (Fin q → ℝ), MeasurableSet S →
      ((cubeMeasure (Fin q) 1) Sᶜ).toReal ≤ δ →
      |(∫ ω, shapeLegalMarkedTilted q source target S r kin g t ω
          ∂twoMarkedCloudLaw q A B α β r) / (r : ℝ) -
        legalMarkedPressure q source target α β r kin g t / (r : ℝ)| < ε := by
  let K := 2 * ((D.count : ℝ) + 1) *
    ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hden : 0 < 2 * K + 1 := by positivity
  let δ := ε / (2 * K + 1)
  have hδ : 0 < δ := div_pos hε hden
  refine ⟨δ, hδ, fun S hS hholes ↦ ?_⟩
  have hbound := D.abs_normalized_shapeLegalMarkedTilted_sub_le hgap q hs ht α β r hr
    hS hsource hsep hC hG hk hkb hg hgb t
  have htol : 2 * δ * K < ε := by
    have heq : δ * (2 * K + 1) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  exact hbound.trans_lt ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hholes (by norm_num : (0 : ℝ) ≤ 2)) hK).trans_lt htol)

end OTSelector.Reconstruction

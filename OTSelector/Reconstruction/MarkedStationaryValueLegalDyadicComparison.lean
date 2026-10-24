import OTSelector.Reconstruction.MarkedStationaryValueLegalDyadic
import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureRegularity

/-!
# Actual dyadic comparison of forward legal pressure

Original strict-clock legal graphs are repaired at the spatial parent scale.
The child defect is the actual original source-only legal deficiency whose
Poisson expectation was proved by finite scalar population types.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- A parent of the actual dyadic cell partition, defined from the proved
global nestedness. Only realized child labels enter the hierarchy. -/
def legalDyadicParent (q k : ℕ) (b : Fin q → Fin (2 ^ (k + 1))) :
    Fin q → Fin (2 ^ k) :=
  if h : ∃ x : Fin q → ℝ, dyadicCell q (k + 1) x = b then
    dyadicCell q k (Classical.choose h)
  else fun _ ↦ 0

theorem legalDyadicParent_cell (q k : ℕ) (x : Fin q → ℝ) :
    legalDyadicParent q k (dyadicCell q (k + 1) x) = dyadicCell q k x := by
  unfold legalDyadicParent
  split
  · rename_i h
    exact dyadicCell_nested_global (Nat.le_succ k) (Classical.choose_spec h)
  · rename_i h
    exact False.elim (h ⟨x, rfl⟩)

/-- The absolute edge budget at the original spatial parent scale. -/
def legalDyadicEdgeBound (q : ℕ) (r C G t : ℝ) (k : ℕ) : ℝ :=
  r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) * (1 / 4 : ℝ) ^ k + |t| * G

theorem legalDyadicEdgeBound_nonneg (q k : ℕ) {r C G t : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G) :
    0 ≤ legalDyadicEdgeBound q r C G t k := by
  unfold legalDyadicEdgeBound
  positivity

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Actual allowed edges sharing a dyadic parent satisfy its quadratic budget. -/
theorem abs_legalMarkedEdge_le_same_dyadic (q k : ℕ)
    (source : A → ℝ) (target : B → ℝ) {r C G : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hpb : ∀ a b, source a < target b → |probe a b| ≤ G)
    (t : ℝ) (ω : TwoMarkedCloudSpace q A B) (i j : ℕ)
    (hS : mSourcePoint ω i ∈ unitCube q) (hT : mTargetPoint ω j ∈ unitCube q)
    (hforward : source (mSourceMark ω i) < target (mTargetMark ω j))
    (hcell : dyadicCell q k (mSourcePoint ω i) = dyadicCell q k (mTargetPoint ω j)) :
    |mKineticCost q r kin ω i j + t * mProbe probe ω i j| ≤
      legalDyadicEdgeBound q r C G t k := by
  have hcoordS (l) : 0 ≤ mSourcePoint ω i l ∧ mSourcePoint ω i l < 1 := by
    have h := Set.mem_pi.mp hS l (mem_univ l)
    exact ⟨h.1.le, h.2⟩
  have hcoordT (l) : 0 ≤ mTargetPoint ω j l ∧ mTargetPoint ω j l < 1 := by
    have h := Set.mem_pi.mp hT l (mem_univ l)
    exact ⟨h.1.le, h.2⟩
  have hsum : ∑ l, (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j) l) ^ 2 ≤
      (q : ℝ) * (1 / 4 : ℝ) ^ k := by
    rw [mDisplacement_eq_sub_of_mem hS hT]
    have heq : (∑ l, (mTargetPoint ω j l - mSourcePoint ω i l) ^ 2) =
        ∑ l, (mSourcePoint ω i l - mTargetPoint ω j l) ^ 2 := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [heq]
    exact sum_sq_le_of_dyadicCell_eq hcoordS hcoordT hcell
  have hkin : |mKineticCost q r kin ω i j| ≤
      r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) * (1 / 4 : ℝ) ^ k := by
    rw [mKineticCost, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr _)]
    calc
      _ ≤ r ^ (2 / (q : ℝ)) * (C * ∑ l,
          (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j) l) ^ 2) :=
        mul_le_mul_of_nonneg_left (hkb _ _ hforward _) (Real.rpow_nonneg hr _)
      _ ≤ r ^ (2 / (q : ℝ)) * (C * ((q : ℝ) * (1 / 4 : ℝ) ^ k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hC)
          (Real.rpow_nonneg hr _)
      _ = _ := by ring
  have hprobe : |t * mProbe probe ω i j| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hpb _ _ hforward) (abs_nonneg t)
  exact (abs_add_le _ _).trans (add_le_add hkin hprobe)

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- A literal actual legal finite cloud satisfies the multiscale comparison.
Finite clock-neighborhood classes are produced internally from its separated
original scalar supports. -/
theorem FiniteScalarBins.legalMarkedTilted_le_dyadic
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    (q : ℕ) (source : A → ℝ) (target : B → ℝ) {r C G : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hpb : ∀ a b, source a < target b → |probe a b| ≤ G)
    (t : ℝ) (ω : TwoMarkedCloudSpace q A B)
    (hS : ∀ i, mSourcePoint ω i ∈ unitCube q)
    (hT : ∀ j, mTargetPoint ω j ∈ unitCube q)
    (hsource : ∀ i, source (mSourceMark ω i) ∈ I)
    (hsep : ∀ i j, δ ≤ |target (mTargetMark ω j) - source (mSourceMark ω i)|)
    (K : ℕ) :
    legalMarkedTilted q source target r kin probe t ω ≤
      (∑ b : Fin q → Fin (2 ^ K), dyadicLegalValue q K source target r kin probe t ω b) +
      ∑ k ∈ Finset.range K,
        (∑ b : Fin q → Fin (2 ^ (k + 1)), dyadicLegalSourceDefect q (k + 1) source target ω b) *
          (2 * ((D.count : ℝ) + 1) * legalDyadicEdgeBound q r C G t k) := by
  have h := D.legalMaximumValue_le_hierarchical_spatial_blocks hδ
    (fun i : Fin (mSourceCount ω) ↦ source (mSourceMark ω i))
    (fun j : Fin (mTargetCount ω) ↦ target (mTargetMark ω j))
    (fun i ↦ hsource i) (fun i j ↦ hsep i j)
    (fun k (i : Fin (mSourceCount ω)) ↦ dyadicCell q k (mSourcePoint ω i))
    (fun k (j : Fin (mTargetCount ω)) ↦ dyadicCell q k (mTargetPoint ω j))
    (legalDyadicParent q) (fun k i ↦ legalDyadicParent_cell q k _)
    (fun k j ↦ legalDyadicParent_cell q k _)
    (fun i j ↦ mKineticCost q r kin ω i j + t * mProbe probe ω i j)
    (legalDyadicEdgeBound q r C G t) (fun k ↦ legalDyadicEdgeBound_nonneg q k hr hC hG)
    (by
      intro k i j hij hcell
      apply abs_legalMarkedEdge_le_same_dyadic q k source target hr hC hkb hpb t ω i j
        (hS i) (hT j) _ hcell
      simpa only [scalarClockLegalGraph, Finset.mem_filter, Finset.mem_univ, true_and] using hij)
    (fun _ ↦ 0) (fun _ ↦ by funext l; apply Fin.ext; exact Nat.mod_one _)
    (fun _ ↦ by funext l; apply Fin.ext; exact Nat.mod_one _) K
  simpa only [legalMarkedTilted, legalMarkedFixedValue, dyadicLegalValue,
    dyadicLegalGraph, dyadicLegalSourceDefect, scalarClockLegalGraph, legalMarkedGraph] using h

/-- An original mark property holds at every actual source-cloud index. -/
theorem ae_all_sourceMarks (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0)
    (P : A → Prop) (hP : ∀ᵐ a ∂α, P a) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q A B α β r, ∀ i : ℕ, P (mSourceMark ω i) := by
  have hA : ∀ᵐ z ∂markedPoissonLaw q A α r, ∀ i : ℕ, P (z.2 i).2 := by
    apply ae_all_iff.mpr
    intro i
    have hp : MeasurePreserving (fun z : MarkedCloudSpace q A ↦ (z.2 i).2)
        (markedPoissonLaw q A α r) α :=
      ⟨by fun_prop, map_markedPoissonLaw_mark q α r i⟩
    exact hp.quasiMeasurePreserving.ae hP
  exact ae_fst_of_ae hA

/-- Original cross-color product-law properties hold simultaneously at all
actual cloud pairs before any matching is selected. -/
theorem ae_all_crossMarks (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0)
    (P : A × B → Prop) (hP : ∀ᵐ p ∂α.prod β, P p) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q A B α β r, ∀ i j : ℕ,
      P (mSourceMark ω i, mTargetMark ω j) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  have hp : MeasurePreserving (fun ω : TwoMarkedCloudSpace q A B ↦
      (mSourceMark ω i, mTargetMark ω j)) (twoMarkedCloudLaw q A B α β r) (α.prod β) :=
    ⟨(measurable_mSourceMark q i).prodMk (measurable_mTargetMark q j),
      map_twoMarkedCloudLaw_mark_pair q α β r i j⟩
  exact hp.quasiMeasurePreserving.ae hP

set_option maxHeartbeats 1200000 in
/-- The original scalar-bin population produces actual dyadic legal pressure
subadditivity, including every leaf expectation and every source-defect term. -/
theorem scalarBinPopulationTypes_legalPressure_le_dyadic
    {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace J] [MeasurableSingletonClass J] [Fintype J]
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ) (hIm : MeasurableSet I)
    [MeasurableSpace (Option (J × Fin D.count × Fin D.count))]
    [MeasurableSingletonClass (Option (J × Fin D.count × Fin D.count))]
    (chart : X × Y → J) (source : X → ℝ) (target : Y → ℝ)
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) (hchart : Measurable chart)
    (hs : Measurable source) (ht : Measurable target)
    (hI : ∀ᵐ p ∂π, source p.1 ∈ I ∧ target p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1)
    (hsep : ∀ᵐ p ∂μ.prod ν, δ ≤ |target p.2 - source p.1|)
    (q : ℕ) (hq : 0 < q) (r : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : X → Y → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : X × Y ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {probe : X → Y → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) (K : ℕ) :
    legalMarkedPressure q source target μ ν r kin probe t ≤
      (((2 ^ K : ℕ) ^ q : ℕ) : ℝ) *
        legalMarkedPressure q source target μ ν (r / ((2 ^ K : ℕ) ^ q : ℝ≥0)) kin probe t +
      ∑ k ∈ Finset.range K,
        Real.sqrt (2 * (r : ℝ) * Fintype.card (Option (J × Fin D.count × Fin D.count)) *
          (((2 ^ (k + 1) : ℕ) ^ q : ℕ) : ℝ)) *
          (2 * ((D.count : ℝ) + 1) * legalDyadicEdgeBound q r C G t k) := by
  have hμI : ∀ᵐ x ∂μ, source x ∈ I := by
    rw [← hπ.1]
    exact (ae_map_iff measurable_fst.aemeasurable (hs hIm)).mpr (hI.mono (fun _ h ↦ h.1))
  have hsource := ae_all_sourceMarks q μ ν r (fun x ↦ source x ∈ I) hμI
  have hsepcloud := ae_all_crossMarks q μ ν r
    (fun p ↦ δ ≤ |target p.2 - source p.1|) hsep
  have hleaf := dyadicLegalValue_sum_integrable_integral q K hq hs ht r μ ν
    hC hG hk hkb hhom hp hpb t
  have hdef (k : ℕ) := scalarBinPopulationTypes_poisson_dyadicSourceDefect_sum D hδ
    chart source target π μ ν hπ hchart hs ht hI hgap q (k + 1) r
  have hrep : Integrable (fun ω : TwoMarkedCloudSpace q X Y ↦
      ∑ k ∈ Finset.range K,
        (∑ b : Fin q → Fin (2 ^ (k + 1)), dyadicLegalSourceDefect q (k + 1) source target ω b) *
          (2 * ((D.count : ℝ) + 1) * legalDyadicEdgeBound q r C G t k))
      (twoMarkedCloudLaw q X Y μ ν r) :=
    integrable_finsetSum _ (fun k _ ↦ (hdef k).1.mul_const _)
  have htotal : Integrable (fun ω : TwoMarkedCloudSpace q X Y ↦
      (∑ b : Fin q → Fin (2 ^ K), dyadicLegalValue q K source target r kin probe t ω b) +
      ∑ k ∈ Finset.range K,
        (∑ b : Fin q → Fin (2 ^ (k + 1)), dyadicLegalSourceDefect q (k + 1) source target ω b) *
          (2 * ((D.count : ℝ) + 1) * legalDyadicEdgeBound q r C G t k))
      (twoMarkedCloudLaw q X Y μ ν r) := hleaf.1.add hrep
  have hpt : ∀ᵐ ω ∂twoMarkedCloudLaw q X Y μ ν r,
      legalMarkedTilted q source target r kin probe t ω ≤
      (∑ b : Fin q → Fin (2 ^ K), dyadicLegalValue q K source target r kin probe t ω b) +
      ∑ k ∈ Finset.range K,
        (∑ b : Fin q → Fin (2 ^ (k + 1)), dyadicLegalSourceDefect q (k + 1) source target ω b) *
          (2 * ((D.count : ℝ) + 1) * legalDyadicEdgeBound q r C G t k) := by
    filter_upwards [ae_points_mem_unitCube_twoMarkedCloudLaw q μ ν r,
      hsource, hsepcloud] with ω hω hsrc hsepω
    exact D.legalMarkedTilted_le_dyadic hδ q source target r.coe_nonneg hC hG
      (fun a b _ ↦ hkb a b) (fun a b _ ↦ hpb a b) t ω hω.1 hω.2 hsrc hsepω K
  have h := integral_mono_ae (integrable_legalMarkedTilted q hs ht μ ν r hC hG
    hk hkb hp hpb t) htotal hpt
  rw [integral_add hleaf.1 hrep, hleaf.2,
    integral_finsetSum _ (fun k _ ↦ (hdef k).1.mul_const _)] at h
  refine h.trans (add_le_add le_rfl (Finset.sum_le_sum ?_))
  intro k _
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (hdef k).2
    (mul_nonneg (by positivity) (legalDyadicEdgeBound_nonneg q k r.coe_nonneg hC hG))

end OTSelector.Reconstruction

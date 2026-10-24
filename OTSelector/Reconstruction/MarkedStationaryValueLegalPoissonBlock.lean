import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonDefect
import OTSelector.Probability.MarkedBlockValueIntegral

/-!
# Actual legal source defects on spatial Poisson subclouds

Only the finite stored cloud prefix is transported.  The raw geometric block
and the measurable encoded block agree almost everywhere; their finite-prefix
law is exactly the original marked Poisson law at the block intensity.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The actual source defect of a finite stored spatial cloud. -/
def blockLegalSourceDefect (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) : ℝ :=
  (dS.1 : ℝ) - PartialMatching.legalMaximumCard
    (scalarClockLegalGraph (fun i ↦ source (dS.2 i).2) (fun j ↦ target (dT.2 j).2))

/-- Restoring the unused tail does not affect any finite-prefix matching. -/
def blockCloudRestore (q : ℕ) [Nonempty A]
    (d : BlockData ((Fin q → ℝ) × A)) : MarkedCloudSpace q A :=
  (d.1, fun j ↦ blockDataEval j d)

theorem measurable_blockCloudRestore (q : ℕ) [Nonempty A] :
    Measurable (blockCloudRestore (A := A) q) :=
  measurable_blockData_fst.prodMk (measurable_pi_lambda _ measurable_blockDataEval)

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem blockLegalSourceDefect_restore (q : ℕ) [Nonempty A] [Nonempty B]
    (source : A → ℝ) (target : B → ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) :
    blockLegalSourceDefect q source target dS dT =
      legalMarkedSourceDefect q source target
        (blockCloudRestore q dS, blockCloudRestore q dT) := by
  unfold blockLegalSourceDefect legalMarkedSourceDefect legalMarkedMaximumCard
  have hg : scalarClockLegalGraph (fun i ↦ source (dS.2 i).2)
      (fun j ↦ target (dT.2 j).2) =
      legalMarkedGraph q dS.1 dT.1 source target
        (blockCloudRestore q dS, blockCloudRestore q dT) := by
    ext p
    simp [scalarClockLegalGraph, legalMarkedGraph, blockCloudRestore, mSourceMark,
      mTargetMark, blockDataEval]
  rw [hg]
  rfl

theorem measurable_blockLegalSourceDefect (q : ℕ) [Nonempty A] [Nonempty B]
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target) :
    Measurable (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      blockLegalSourceDefect q source target d.1 d.2) := by
  have hm : Measurable (legalMarkedSourceDefect q source target) :=
    (measurable_from_nat.comp (measurable_mSourceCount q)).sub
      (measurable_legalMarkedMaximumCard_cast q hs ht)
  have h := hm.comp (((measurable_blockCloudRestore q).comp measurable_fst).prodMk
    ((measurable_blockCloudRestore q).comp measurable_snd))
  change Measurable (fun d : BlockData ((Fin q → ℝ) × A) ×
      BlockData ((Fin q → ℝ) × B) ↦ legalMarkedSourceDefect q source target
    (blockCloudRestore q d.1, blockCloudRestore q d.2)) at h
  simpa only [← blockLegalSourceDefect_restore] using h

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem blockLegalSourceDefect_cloudPrefix (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    blockLegalSourceDefect q source target
      (⟨ω.1.1, fun i : Fin ω.1.1 ↦ ω.1.2 i⟩ : BlockData ((Fin q → ℝ) × A))
      (⟨ω.2.1, fun j : Fin ω.2.1 ↦ ω.2.2 j⟩ : BlockData ((Fin q → ℝ) × B)) =
      legalMarkedSourceDefect q source target ω := rfl

/-- Every measurable finite-prefix observable has the exact original local
Poisson expectation, and integrability transfers to the raw geometric block. -/
theorem blockLocalCloud_integrable_integral_prefix (q m : ℕ) (hm : 0 < m)
    (r : ℝ≥0) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (b : Fin q → Fin m)
    (F : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) → ℝ)
    (hF : Measurable F)
    (hI : Integrable (fun ω : TwoMarkedCloudSpace q A B ↦
      F (⟨ω.1.1, fun i : Fin ω.1.1 ↦ ω.1.2 i⟩,
        ⟨ω.2.1, fun j : Fin ω.2.1 ↦ ω.2.2 j⟩))
      (twoMarkedCloudLaw q A B α β (r / (m ^ q : ℝ≥0)))) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B ↦
      F (blockLocalCloud q m b ω.1, blockLocalCloud q m b ω.2))
      (twoMarkedCloudLaw q A B α β r) ∧
    (∫ ω, F (blockLocalCloud q m b ω.1, blockLocalCloud q m b ω.2)
      ∂twoMarkedCloudLaw q A B α β r) =
      ∫ ω : TwoMarkedCloudSpace q A B,
        F (⟨ω.1.1, fun i : Fin ω.1.1 ↦ ω.1.2 i⟩,
          ⟨ω.2.1, fun j : Fin ω.2.1 ↦ ω.2.2 j⟩)
        ∂twoMarkedCloudLaw q A B α β (r / (m ^ q : ℝ≥0)) := by
  have : NeZero m := ⟨hm.ne'⟩
  let enc : TwoMarkedCloudSpace q A B →
      BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) :=
    Prod.map (blockLocalCloudEncoded q m b) (blockLocalCloudEncoded q m b)
  let mk : TwoMarkedCloudSpace q A B →
      BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) :=
    Prod.map (fun ω ↦ ⟨ω.1, fun i : Fin ω.1 ↦ ω.2 i⟩)
      (fun ω ↦ ⟨ω.1, fun j : Fin ω.1 ↦ ω.2 j⟩)
  have henc : Measurable enc :=
    ((measurable_blockLocalCloudEncoded q m b).comp measurable_fst).prodMk
      ((measurable_blockLocalCloudEncoded q m b).comp measurable_snd)
  have hmk : Measurable mk := ((measurable_blockDataMk q A).comp measurable_fst).prodMk
    ((measurable_blockDataMk q B).comp measurable_snd)
  have hlaw : (twoMarkedCloudLaw q A B α β r).map enc =
      (twoMarkedCloudLaw q A B α β (r / (m ^ q : ℝ≥0))).map mk := by
    unfold twoMarkedCloudLaw
    dsimp only [enc, mk]
    rw [← Measure.map_prod_map _ _ (measurable_blockLocalCloudEncoded q m b)
      (measurable_blockLocalCloudEncoded q m b)]
    rw [blockLocalCloudEncoded_law' q m hm r α b,
      blockLocalCloudEncoded_law' q m hm r β b]
    exact Measure.map_prod_map _ _ (measurable_blockDataMk q A) (measurable_blockDataMk q B)
  have hImap : Integrable F ((twoMarkedCloudLaw q A B α β r).map enc) := by
    rw [hlaw]
    exact (integrable_map_measure hF.aestronglyMeasurable hmk.aemeasurable).mpr hI
  have hIenc : Integrable (fun ω ↦ F (enc ω)) (twoMarkedCloudLaw q A B α β r) :=
    hImap.comp_measurable henc
  have hae : (fun ω : TwoMarkedCloudSpace q A B ↦
      F (blockLocalCloud q m b ω.1, blockLocalCloud q m b ω.2)) =ᵐ[
        twoMarkedCloudLaw q A B α β r] fun ω ↦ F (enc ω) := by
    filter_upwards [ae_fst_of_ae (blockLocalCloud_ae_eq_encoded q m hm r α b),
      ae_snd_of_ae (blockLocalCloud_ae_eq_encoded q m hm r β b)] with ω hS hT
    simp only [enc, hS, hT]
    rfl
  refine ⟨hIenc.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, ← integral_map henc.aemeasurable hF.aestronglyMeasurable,
    hlaw, integral_map hmk.aemeasurable hF.aestronglyMeasurable]
  rfl

/-- The legal source defect of the literal spatial subcloud has precisely the
original Poisson expectation at the local intensity. -/
theorem blockLocalCloud_legalSourceDefect (q m : ℕ) (hm : 0 < m)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (r : ℝ≥0) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (b : Fin q → Fin m) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B ↦ blockLegalSourceDefect q source target
      (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2))
      (twoMarkedCloudLaw q A B α β r) ∧
    (∫ ω, blockLegalSourceDefect q source target
      (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2)
      ∂twoMarkedCloudLaw q A B α β r) =
      ∫ ω, legalMarkedSourceDefect q source target ω
        ∂twoMarkedCloudLaw q A B α β (r / (m ^ q : ℝ≥0)) := by
  let : Nonempty A := nonempty_of_isProbabilityMeasure α
  let : Nonempty B := nonempty_of_isProbabilityMeasure β
  have h := blockLocalCloud_integrable_integral_prefix q m hm r α β b
    (fun d ↦ blockLegalSourceDefect q source target d.1 d.2)
    (measurable_blockLegalSourceDefect q hs ht)
    (by simpa only [blockLegalSourceDefect_cloudPrefix] using
      integrable_legalMarkedSourceDefect q hs ht α β (r / (m ^ q : ℝ≥0)))
  simpa only [blockLegalSourceDefect_cloudPrefix] using h

/-- The original scalar-bin population supplies a square-root source-defect
bound in every actual spatial block, under the unchanged original cloud law. -/
theorem scalarBinPopulationTypes_poisson_blockSourceDefect
    {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace J] [MeasurableSingletonClass J] [Fintype J]
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    [MeasurableSpace (Option (J × Fin D.count × Fin D.count))]
    [MeasurableSingletonClass (Option (J × Fin D.count × Fin D.count))]
    (chart : X × Y → J) (source : X → ℝ) (target : Y → ℝ)
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) (hchart : Measurable chart)
    (hs : Measurable source) (ht : Measurable target)
    (hI : ∀ᵐ p ∂π, source p.1 ∈ I ∧ target p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1)
    (q m : ℕ) (hm : 0 < m) (r : ℝ≥0) (b : Fin q → Fin m) :
    Integrable (fun ω : TwoMarkedCloudSpace q X Y ↦ blockLegalSourceDefect q source target
      (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2))
      (twoMarkedCloudLaw q X Y μ ν r) ∧
    (∫ ω, blockLegalSourceDefect q source target
      (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2)
      ∂twoMarkedCloudLaw q X Y μ ν r) ≤
      Real.sqrt (2 * ((r / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ) *
        Fintype.card (Option (J × Fin D.count × Fin D.count))) := by
  obtain ⟨hIblock, heq⟩ := blockLocalCloud_legalSourceDefect q m hm hs ht r μ ν b
  obtain ⟨-, hbound⟩ := scalarBinPopulationTypes_poisson_sourceDefect D hδ chart source
    target π μ ν hπ hchart hs ht hI hgap q (r / (m ^ q : ℝ≥0))
  exact ⟨hIblock, heq.trans_le hbound⟩

/-- The actual legal tilted minimum on two stored finite spatial clouds. -/
def blockLegalTilted (q : ℕ) (source : A → ℝ) (target : B → ℝ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) : ℝ :=
  PartialMatching.legalMaximumValue
    (scalarClockLegalGraph (fun i ↦ source (dS.2 i).2) (fun j ↦ target (dT.2 j).2))
    (fun i j ↦ r ^ (2 / (q : ℝ)) * kin (dS.2 i).2 (dT.2 j).2
      (mDisplacement (dS.2 i).1 (dT.2 j).1) + t * probe (dS.2 i).2 (dT.2 j).2)

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem blockLegalTilted_restore (q : ℕ) [Nonempty A] [Nonempty B]
    (source : A → ℝ) (target : B → ℝ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) :
    blockLegalTilted q source target r kin probe t dS dT =
      legalMarkedTilted q source target r kin probe t
        (blockCloudRestore q dS, blockCloudRestore q dT) := by
  have hS (i : Fin dS.1) :
      (blockCloudRestore q dS).2 i = dS.2 i := by simp [blockCloudRestore, blockDataEval]
  have hT (j : Fin dT.1) :
      (blockCloudRestore q dT).2 j = dT.2 j := by simp [blockCloudRestore, blockDataEval]
  unfold blockLegalTilted legalMarkedTilted legalMarkedFixedValue
  have hg : scalarClockLegalGraph (fun i ↦ source (dS.2 i).2)
      (fun j ↦ target (dT.2 j).2) =
      legalMarkedGraph q dS.1 dT.1 source target
        (blockCloudRestore q dS, blockCloudRestore q dT) := by
    ext p
    simp [scalarClockLegalGraph, legalMarkedGraph, blockCloudRestore, mSourceMark,
      mTargetMark, blockDataEval]
  rw [hg]
  congr 1
  funext i j
  simp [mKineticCost, mProbe, mSourceMark, mTargetMark, mSourcePoint, mTargetPoint,
    hS, hT]

theorem measurable_blockLegalTilted (q : ℕ) [Nonempty A] [Nonempty B]
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (r : ℝ) {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe)) (t : ℝ) :
    Measurable (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      blockLegalTilted q source target r kin probe t d.1 d.2) := by
  have h := (measurable_legalMarkedTilted q hs ht hk hp r t).comp
    (((measurable_blockCloudRestore q).comp measurable_fst).prodMk
      ((measurable_blockCloudRestore q).comp measurable_snd))
  change Measurable (fun d : BlockData ((Fin q → ℝ) × A) ×
      BlockData ((Fin q → ℝ) × B) ↦ legalMarkedTilted q source target r kin probe t
        (blockCloudRestore q d.1, blockCloudRestore q d.2)) at h
  simpa only [← blockLegalTilted_restore] using h

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem blockLegalTilted_cloudPrefix (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    blockLegalTilted q source target r kin probe t
      (⟨ω.1.1, fun i : Fin ω.1.1 ↦ ω.1.2 i⟩ : BlockData ((Fin q → ℝ) × A))
      (⟨ω.2.1, fun j : Fin ω.2.1 ↦ ω.2.2 j⟩ : BlockData ((Fin q → ℝ) × B)) =
      legalMarkedTilted q source target r kin probe t ω := rfl

/-- The mean actual legal block value is the actual legal pressure at its local
intensity. The finite prefix transport does not assume a law for unused tails. -/
theorem blockLocalCloud_legalTilted_integral (q m : ℕ) (hm : 0 < m)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (r : ℝ≥0) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (b : Fin q → Fin m)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B ↦ blockLegalTilted q source target
      ((r / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ) kin probe t
      (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2))
      (twoMarkedCloudLaw q A B α β r) ∧
    (∫ ω, blockLegalTilted q source target ((r / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ) kin probe t
      (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2)
      ∂twoMarkedCloudLaw q A B α β r) =
      legalMarkedPressure q source target α β (r / (m ^ q : ℝ≥0)) kin probe t := by
  let : Nonempty A := nonempty_of_isProbabilityMeasure α
  let : Nonempty B := nonempty_of_isProbabilityMeasure β
  have h := blockLocalCloud_integrable_integral_prefix q m hm r α β b
    (fun d ↦ blockLegalTilted q source target ((r / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ)
      kin probe t d.1 d.2)
    (measurable_blockLegalTilted q hs ht _ hk hp t)
    (by simpa only [blockLegalTilted_cloudPrefix] using
      integrable_legalMarkedTilted q hs ht α β (r / (m ^ q : ℝ≥0)) hC hG hk hkb hp hpb t)
  simpa only [blockLegalTilted_cloudPrefix, legalMarkedPressure] using h

end OTSelector.Reconstruction

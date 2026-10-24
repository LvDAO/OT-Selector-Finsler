import OTSelector.Reconstruction.FinslerRelativeLawOriginalPrefixClassValue
import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineShape

/-! The canonical original retained optimizer reads true untruncated coordinates. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The raw-coordinate frozen score on the unchanged original endpoint indices. -/
def originalCellRawClassScore
    {X C T : Type*} {A B : C → Type*} {q N : ℕ}
    (readS : ∀ c, X → (Fin q → ℝ) × A c) (readT : ∀ c, X → (Fin q → ℝ) × B c)
    (r : C → ℝ) (kin : ∀ c, A c → B c → (Fin q → ℝ) → ℝ)
    (probe : ∀ c, A c → B c → ℝ) (tilt : ℝ) (c : C)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T)))
    (i j : Fin N) : ℝ :=
  r c ^ (2 / (q : ℝ)) * kin c (readS c (sample.1 i).1).2 (readT c (sample.2 j).1).2
    (fun l ↦ (readT c (sample.2 j).1).1 l - (readS c (sample.1 i).1).1 l) +
      tilt * probe c (readS c (sample.1 i).1).2 (readT c (sample.2 j).1).2

/-- The literal raw-coordinate value is measurable without imposing a spatial
carrier. Reading positions as extra marks avoids any truncation in this proof. -/
theorem measurable_unclampedBlockLegalTilted (q : ℕ)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [Nonempty A] [Nonempty B]
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (r : ℝ) {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe)) (tilt : ℝ) :
    Measurable (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      unclampedBlockLegalTilted q source target r kin probe tilt d.1 d.2) := by
  let injectS : ((Fin q → ℝ) × A) → (Fin q → ℝ) × ((Fin q → ℝ) × A) := fun p ↦ (0, p)
  let injectT : ((Fin q → ℝ) × B) → (Fin q → ℝ) × ((Fin q → ℝ) × B) := fun p ↦ (0, p)
  have hS : Measurable injectS := measurable_const.prodMk measurable_id
  have hT : Measurable injectT := measurable_const.prodMk measurable_id
  let rawKin := fun (p : (Fin q → ℝ) × A) (p' : (Fin q → ℝ) × B) (_ : Fin q → ℝ) ↦
    kin p.2 p'.2 (fun l ↦ p'.1 l - p.1 l)
  let rawProbe := fun (p : (Fin q → ℝ) × A) (p' : (Fin q → ℝ) × B) ↦ probe p.2 p'.2
  have hrawKin : Measurable (Function.uncurry (fun p : ((Fin q → ℝ) × A) × ((Fin q → ℝ) × B) ↦ rawKin p.1 p.2)) := by
    change Measurable (fun p : (((Fin q → ℝ) × A) × ((Fin q → ℝ) × B)) × (Fin q → ℝ) ↦
      kin p.1.1.2 p.1.2.2 (fun l ↦ p.1.2.1 l - p.1.1.1 l))
    apply hk.comp
      (show Measurable (fun p : (((Fin q → ℝ) × A) × ((Fin q → ℝ) × B)) × (Fin q → ℝ) ↦
        ((p.1.1.2, p.1.2.2), fun l ↦ p.1.2.1 l - p.1.1.1 l)) from by fun_prop)
  have hrawProbe : Measurable (Function.uncurry rawProbe) := by
    change Measurable (fun p : ((Fin q → ℝ) × A) × ((Fin q → ℝ) × B) ↦ probe p.1.2 p.2.2)
    exact hp.comp (measurable_fst.snd.prodMk measurable_snd.snd)
  have hm := (measurable_blockLegalTilted (kin := rawKin) (probe := rawProbe) q (hs.comp measurable_snd) (ht.comp measurable_snd)
    r hrawKin hrawProbe tilt).comp
      ((measurable_mapBlockData hS).prodMap (measurable_mapBlockData hT))
  exact hm

/-- Restricting the original graph and reading the true endpoint displacement
commutes exactly with the signed legal finite value. -/
theorem originalRetainedCellGraph_raw_value_eq_unclampedBlockLegalTilted
    {X Z C T : Type*} {A B : C → Type*} {q N : ℕ}
    (a : X → Z) (cell : C → Set Z)
    (readS : ∀ c, X → (Fin q → ℝ) × A c) (readT : ∀ c, X → (Fin q → ℝ) × B c)
    (source : ∀ c, A c → ℝ) (target : ∀ c, B c → ℝ)
    (r : C → ℝ) (kin : ∀ c, A c → B c → (Fin q → ℝ) → ℝ)
    (probe : ∀ c, A c → B c → ℝ) (tilt : ℝ) (c : C)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) :
    let extra := originalCellScalarClassGraph readS readT source target
    let model := originalCellRawClassScore readS readT r kin probe tilt
    let dataS := mapBlockData (fun p ↦ readS c p.1)
      (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.1)
    let dataT := mapBlockData (fun p ↦ readT c p.1)
      (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.2)
    PartialMatching.legalMaximumValue (originalRetainedCellGraph a cell extra c sample) (model c sample) =
      unclampedBlockLegalTilted q (source c) (target c) (r c) (kin c) (probe c) tilt dataS dataT := by
  have h := originalRetainedCellGraph_value_eq_prefix a cell
    (originalCellScalarClassGraph readS readT source target)
    (originalCellRawClassScore readS readT r kin probe tilt) c sample
  dsimp only at h ⊢
  rw [originalCellScalarClassGraph, PartialMatching.inducedLegalGraph_scalarClockLegalGraph] at h
  simpa only [unclampedBlockLegalTilted, mapBlockData, finiteOriginalRestrictedData_point,
    originalCellRawClassScore, Function.comp_def] using h

/-- The canonical original-index optimizer realizes the literal raw-prefix
legal value, so physical affine coordinates never require cube truncation. -/
theorem originalRetainedCellOptimizer_raw_model_cost_eq_unclampedBlockLegalTilted
    {X Z C T : Type*} {A B : C → Type*} {q N : ℕ}
    (a : X → Z) (cell : C → Set Z)
    (readS : ∀ c, X → (Fin q → ℝ) × A c) (readT : ∀ c, X → (Fin q → ℝ) × B c)
    (source : ∀ c, A c → ℝ) (target : ∀ c, B c → ℝ)
    (r : C → ℝ) (kin : ∀ c, A c → B c → (Fin q → ℝ) → ℝ)
    (probe : ∀ c, A c → B c → ℝ) (tilt : ℝ) (c : C)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) :
    let extra := originalCellScalarClassGraph readS readT source target
    let model := originalCellRawClassScore readS readT r kin probe tilt
    let dataS := mapBlockData (fun p ↦ readS c p.1)
      (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.1)
    let dataT := mapBlockData (fun p ↦ readT c p.1)
      (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.2)
    (originalRetainedCellOptimizer a cell extra model c sample).cost (model c sample) =
      unclampedBlockLegalTilted q (source c) (target c) (r c) (kin c) (probe c) tilt dataS dataT := by
  exact (originalRetainedCellOptimizer_isLegalOptimal a cell _ _ c sample).2.2.trans
    (originalRetainedCellGraph_raw_value_eq_unclampedBlockLegalTilted a cell readS readT source target
      r kin probe tilt c sample)

end OTSelector.Reconstruction

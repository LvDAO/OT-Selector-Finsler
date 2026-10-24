import OTSelector.Finite.CommonSampleMatchingCore
import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyShifted
import OTSelector.Reconstruction.FinslerRelativeLawLegalRepair
import OTSelector.Finite.MeasurableLegalOptimizer
import OTSelector.Reconstruction.MarkedStationaryValueLegalCloud

/-!
# Adaptive repair inputs from the actual exact legal optimizer

The core is the first actual signed legal optimum, restricted to endpoints
left unchanged by common sampling. Its edge events follow from the original
measurable graph, costs, and sample coordinates. No independent measurability
hypothesis for an adaptively selected matching is needed.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability

/-- Actual signed legal optimum on fixed prefixes of the original marked cloud. -/
def firstLegalMarkedOptimalMatching {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (q m n : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) : OTSelector.PartialMatching m n :=
  PartialMatching.firstLegalOptimalMatching (legalMarkedGraph q m n sourceClock targetClock ω)
    (fun i j ↦ mKineticCost q r kin ω i j + t * mProbe g ω i j)

theorem firstLegalMarkedOptimalMatching_isLegalOptimal
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (q m n : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    PartialMatching.IsLegalOptimal (legalMarkedGraph q m n sourceClock targetClock ω)
      (fun i j ↦ mKineticCost q r kin ω i j + t * mProbe g ω i j)
      (firstLegalMarkedOptimalMatching q m n sourceClock targetClock r kin g t ω) :=
  PartialMatching.firstLegalOptimalMatching_isLegalOptimal _ _

/-- Actual marked clocks, kinetic energy, and probes discharge all selected-core
edge measurability events, including ties among exact signed optima. -/
theorem measurableSet_mem_firstLegalMarkedOptimalMatching
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (q m n : ℕ) {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hsource : Measurable sourceClock) (htarget : Measurable targetClock)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g)) (r t : ℝ)
    (e : Fin m × Fin n) :
    MeasurableSet {ω : TwoMarkedCloudSpace q A B |
      e ∈ (firstLegalMarkedOptimalMatching q m n sourceClock targetClock r kin g t ω).edges} := by
  apply PartialMatching.measurableSet_mem_firstLegalOptimalMatching
    (legalMarkedGraph q m n sourceClock targetClock)
    (measurableSet_legalMarkedGraph_eq q m n hsource htarget)
    (fun ω i j ↦ mKineticCost q r kin ω i j + t * mProbe g ω i j)
  intro i j
  exact (measurable_mKineticCost q r hkin i j).add
    ((measurable_mProbe q hg i j).const_mul t)

/-- The exact model legal optimum restricted to the common-sampling endpoints. -/
def firstLegalOptimalCommonCore {Ω S T : Type*} {m n : ℕ}
    (allowed : Ω → Finset (Fin m × Fin n)) (score : Ω → Fin m → Fin n → ℝ)
    (sa sb : Fin m → Ω → S) (ta tb : Fin n → Ω → T) (ω : Ω) :
    OTSelector.PartialMatching m n :=
  commonSampleMatching (PartialMatching.firstLegalOptimalMatching (allowed ω) (score ω))
    (fun i ↦ sa i ω) (fun i ↦ sb i ω) (fun j ↦ ta j ω) (fun j ↦ tb j ω)

/-- Common-sampling restriction preserves measurable edge events of the actual
optimizer. Adaptively selected partners are never assigned a new iid law. -/
theorem measurableSet_mem_firstLegalOptimalCommonCore
    {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableEq S] [MeasurableEq T] {m n : ℕ}
    (allowed : Ω → Finset (Fin m × Fin n))
    (hallowed : ∀ E, MeasurableSet {ω | allowed ω = E})
    (score : Ω → Fin m → Fin n → ℝ) (hscore : ∀ i j, Measurable (fun ω ↦ score ω i j))
    (sa sb : Fin m → Ω → S) (ta tb : Fin n → Ω → T)
    (hsa : ∀ i, Measurable (sa i)) (hsb : ∀ i, Measurable (sb i))
    (hta : ∀ j, Measurable (ta j)) (htb : ∀ j, Measurable (tb j))
    (e : Fin m × Fin n) :
    MeasurableSet {ω | e ∈ (firstLegalOptimalCommonCore allowed score sa sb ta tb ω).edges} := by
  classical
  have heq : {ω | e ∈ (firstLegalOptimalCommonCore allowed score sa sb ta tb ω).edges} =
      {ω | e ∈ (PartialMatching.firstLegalOptimalMatching (allowed ω) (score ω)).edges} ∩
      ({ω | sa e.1 ω = sb e.1 ω} ∩ {ω | ta e.2 ω = tb e.2 ω}) := by
    ext ω
    simp [firstLegalOptimalCommonCore, commonSampleMatching,
      OTSelector.PartialMatching.commonSampleCore]
  rw [heq]
  exact (PartialMatching.measurableSet_mem_firstLegalOptimalMatching allowed hallowed
    score hscore e).inter ((measurableSet_eq_fun (hsa e.1) (hsb e.1)).inter
      (measurableSet_eq_fun (hta e.2) (htb e.2)))

/-- The explicit phase-averaged repair budget for the actual exact-optimal common core.
All selected-core measurability is proved from the original graph, score and
coordinate observations. -/
theorem integral_shifted_firstLegalOptimalCommonCoreBudget_le
    {Ω Θ S T : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableEq S] [MeasurableEq T]
    {K N q : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    [∀ k, MeasurableSpace (C k)] [∀ k, MeasurableSingletonClass (C k)]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Θ) [IsProbabilityMeasure Q]
    (μ : Measure (Fin q → ℝ)) [IsProbabilityMeasure μ]
    (allowed : Ω → Finset (Fin N × Fin N))
    (hallowed : ∀ E, MeasurableSet {ω | allowed ω = E})
    (score : Ω → Fin N → Fin N → ℝ) (hscore : ∀ i j, Measurable (fun ω ↦ score ω i j))
    (sa sb : Fin N → Ω → S) (ta tb : Fin N → Ω → T)
    (hsa : ∀ i, Measurable (sa i)) (hsb : ∀ i, Measurable (sb i))
    (hta : ∀ j, Measurable (ta j)) (htb : ∀ j, Measurable (tb j))
    (xs ys : Fin N → Ω → Fin q → ℝ)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω i ↦ ys i ω) P)
    (ell : Fin K → ℝ) (hell : ∀ k, 0 < ell k)
    (phase : Fin K → Θ → Fin q → ℝ) (hp : ∀ k, Measurable (phase k))
    (hlaw : ∀ k, Q.map (phase k) = shiftedGridPhaseLaw q (ell k))
    (readout : (k : Fin K) → (Fin q → ℤ) → C k) (hr : ∀ k, Measurable (readout k))
    (base : ℝ) (weight : Fin K → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (hdisp : Integrable (fun ω ↦ retainedCoordinateDisplacement (firstLegalOptimalCommonCore allowed score sa sb ta tb ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)) P) :
    Integrable (fun p : Ω × Θ ↦ adaptiveOrphanRepairBudget (firstLegalOptimalCommonCore allowed score sa sb ta tb p.1)
      (shiftedHierarchyCell ell phase readout p.2)
      (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) base weight) (P.prod Q) ∧
    (∫ p : Ω × Θ, adaptiveOrphanRepairBudget (firstLegalOptimalCommonCore allowed score sa sb ta tb p.1)
      (shiftedHierarchyCell ell phase readout p.2)
      (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) base weight ∂(P.prod Q)) ≤
      (∫ ω, (N : ℝ) - (firstLegalOptimalCommonCore allowed score sa sb ta tb ω).card ∂P) * base +
        (1 / 2 : ℝ) * ∑ k, weight k * Real.sqrt (2 * (N : ℝ) * Fintype.card (C k)) +
        (∫ ω, retainedCoordinateDisplacement (firstLegalOptimalCommonCore allowed score sa sb ta tb ω)
          (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) * ∑ k, weight k / ell k := by
  exact integral_shifted_adaptiveOrphanRepairBudget_le P Q μ
    (firstLegalOptimalCommonCore allowed score sa sb ta tb)
    (measurableSet_mem_firstLegalOptimalCommonCore allowed hallowed score hscore sa sb ta tb
      hsa hsb hta htb) xs ys hx hy hxi hyi hxl hyl hxy ell hell phase hp hlaw readout hr
    base weight hw hdisp

/-- The actual common core's missing cardinality is exactly controlled by
legal maximum-cardinality deficit and the original endpoint mismatch counts. -/
theorem firstLegalOptimalCommonCore_missing_le
    {Ω S T : Type*} {N : ℕ}
    (allowed : Ω → Finset (Fin N × Fin N)) (score : Ω → Fin N → Fin N → ℝ)
    (sa sb : Fin N → Ω → S) (ta tb : Fin N → Ω → T) (ω : Ω) :
    (N : ℝ) - (firstLegalOptimalCommonCore allowed score sa sb ta tb ω).card ≤
      (N : ℝ) - PartialMatching.legalMaximumCard (allowed ω) +
        diffCount N (fun i ↦ (sa i ω, sb i ω)) +
        diffCount N (fun j ↦ (ta j ω, tb j ω)) := by
  classical
  let σ := PartialMatching.firstLegalOptimalMatching (allowed ω) (score ω)
  have hsub := OTSelector.PartialMatching.commonSampleCore_subset σ
    (fun i ↦ sa i ω) (fun i ↦ sb i ω) (fun j ↦ ta j ω) (fun j ↦ tb j ω)
  have hlost := OTSelector.PartialMatching.card_sdiff_commonSampleCore_le σ
    (fun i ↦ sa i ω) (fun i ↦ sb i ω) (fun j ↦ ta j ω) (fun j ↦ tb j ω)
  rw [Finset.card_sdiff_of_subset hsub] at hlost
  have hreal := Nat.cast_le (α := ℝ).mpr hlost
  rw [Nat.cast_sub (Finset.card_le_card hsub), Nat.cast_add] at hreal
  have hσ : σ.card = PartialMatching.legalMaximumCard (allowed ω) :=
    (PartialMatching.firstLegalOptimalMatching_isLegalOptimal (allowed ω) (score ω)).2.1
  change (σ.card : ℝ) - (firstLegalOptimalCommonCore allowed score sa sb ta tb ω).card ≤
    diffCount N (fun i ↦ (sa i ω, sb i ω)) +
    diffCount N (fun j ↦ (ta j ω, tb j ω)) at hreal
  rw [hσ] at hreal
  linarith

end OTSelector.Reconstruction

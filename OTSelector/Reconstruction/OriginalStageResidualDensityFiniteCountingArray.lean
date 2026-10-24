import OTSelector.Reconstruction.OriginalStageResidualDensityExcessCountEvent
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputSimpleCarrier

/-! Actual finite integer measures admit original finite-array representations. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess

/-- Finiteness of a genuine integer configuration forces all but finitely many shells empty. -/
theorem originalFiniteCounting_shells_eventually_empty
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {base : X}
    (c : LocalConfiguration base) (hfinite : LocalConfiguration.countingMeasure c univ < ∞) :
    ∃ N : ℕ, ∀ n, N ≤ n → c n = 0 := by
  have hmass (n : ℕ) : LocalConfiguration.shellMeasure c n univ = ((c n).card : ℝ≥0∞) := by
    rw [LocalConfiguration.shellMeasure_apply c n MeasurableSet.univ]
    simp
  have hsum : (∑' n, ((c n).card : ℝ≥0∞)) ≠ ∞ := by
    simpa only [LocalConfiguration.countingMeasure_apply c MeasurableSet.univ, hmass] using hfinite.ne
  have hS := ENNReal.finite_const_le_of_tsum_ne_top hsum (ε := 1) one_ne_zero
  obtain ⟨N, hN⟩ := hS.toFinset.exists_nat_subset_range
  refine ⟨N, fun n hn ↦ ?_⟩
  by_contra hne
  have hcard : 1 ≤ (c n).card := Nat.one_le_iff_ne_zero.mpr (fun hz ↦ hne (Multiset.card_eq_zero.mp hz))
  have hmem : n ∈ hS.toFinset := hS.mem_toFinset.mpr (by exact_mod_cast hcard)
  have := Finset.mem_range.mp (hN hmem)
  omega

/-- The actual finite integer measure is precisely a finite tuple of its unchanged atoms.
This produces a representation, with no sampling, spatial-law or count conclusion assumed. -/
theorem exists_originalFiniteCountingArray
    {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (base : X) (μ : LocalFiniteMeasure X)
    (hcount : IsLegalCountingMeasure base μ) (hfinite : (μ : Measure X) univ < ∞) :
    ∃ (n : ℕ) (points : Fin n → X), (μ : Measure X) = ∑ i, Measure.dirac (points i) := by
  obtain ⟨c, hc⟩ := hcount
  have heq : LocalConfiguration.countingMeasure c = (μ : Measure X) := congrArg Subtype.val hc
  obtain ⟨N, hN⟩ := originalFiniteCounting_shells_eventually_empty c (heq ▸ hfinite)
  have hmeasure : LocalConfiguration.countingMeasure c =
      ((LocalConfiguration.window c N).map Measure.dirac).sum := by
    rw [LocalConfiguration.sum_map_window]
    change LocalConfiguration.countingMeasure c = ∑ n ∈ Finset.range N,
      LocalConfiguration.shellMeasure c n
    ext U hU
    rw [LocalConfiguration.countingMeasure_apply c hU, Measure.finsetSum_apply]
    apply tsum_eq_sum
    intro n hn
    have hn' : N ≤ n := le_of_not_gt (by simpa only [Finset.mem_range] using hn)
    simp [LocalConfiguration.shellMeasure, hN n hn']
  let l := (LocalConfiguration.window c N).toList
  refine ⟨l.length, l.get, ?_⟩
  rw [← heq, hmeasure]
  rw [← Multiset.coe_toList (LocalConfiguration.window c N), Multiset.map_coe, Multiset.sum_coe]
  change (l.map Measure.dirac).sum = ∑ i, Measure.dirac (l.get i)
  calc
    (l.map Measure.dirac).sum =
        (List.ofFn (fun i : Fin l.length ↦ Measure.dirac (l.get i))).sum := by
      have heq : (List.ofFn l.get).map Measure.dirac = List.ofFn (Measure.dirac ∘ l.get) := List.map_ofFn
      simpa only [Function.comp_def, List.ofFn_get] using congrArg List.sum heq
    _ = _ := List.sum_ofFn

/-- A finite original marked-point measure has an actual MarkedCloudSpace representation
on its unchanged finite atoms, with the reserve readout using precisely those original Fin indices. -/
theorem exists_originalFiniteMarkedCloud
    {q : ℕ} (μ : Measure (LegalMarkedPhysicalPoint q))
    (harray : ∃ (n : ℕ) (points : Fin n → LegalMarkedPhysicalPoint q), μ = ∑ i, Measure.dirac (points i)) :
    ∃ z : MarkedCloudSpace q ℝ, μ = originalStageRemainingReserveMeasure z Finset.univ := by
  obtain ⟨n, points, hpoints⟩ := harray
  let z : MarkedCloudSpace q ℝ := ⟨n, fun j ↦ if h : j < n then points ⟨j, h⟩ else 0⟩
  refine ⟨z, ?_⟩
  rw [hpoints]
  unfold originalStageRemainingReserveMeasure
  apply Finset.sum_congr rfl
  intro i _
  have hi : (i : ℕ) < n := i.2
  simp [z, hi]

end OTSelector.Reconstruction

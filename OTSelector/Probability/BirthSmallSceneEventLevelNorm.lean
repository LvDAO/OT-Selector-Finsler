import OTSelector.MeasureTheory.Lp.FiniteGoodBadSum
import OTSelector.Probability.BirthSmallTrafficInterpolatedNorm
import OTSelector.Probability.BirthRankZeroInterpolatedNorm

/-! The literal small-phase traffic of each original birth level has its own
interpolated energy profile plus its actual same-scene count-tail contribution. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- The actual positiveRank finite band sum retains its true scene-small event,
its own count-good energy estimates and its original count-tail norm. -/
theorem birthBand_positiveRank_sceneEvent_traffic_level_norm
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (Small Bad : ι → Set Ω) (T : ι → Ω → ℝ)
    (hgood : ∀ i ∈ bands, MemLp (((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i)) 2 P)
    (hbad : ∀ i ∈ bands, MemLp ((Bad i).indicator ((Small i).indicator (T i))) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {E t s C k B c K : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s) (hC : 0 ≤ C)
    (hE1 : 1 ≤ E) (hk : 0 < k) (hB : 0 ≤ B)
    (hNs : (bands.card : ℝ) * s = 8 * t)
    (hE : (∑ i ∈ bands, e i) ≤ E)
    (hV : (∑ i ∈ bands, v i) ≤ E)
    (hfirst : ∀ i ∈ bands, (∫ x, (((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i) x) ^ 2 ∂P) ≤
      C * s ^ (3 / 2 : ℝ) *
        (t ^ ((k - 3) / 2) * Real.sqrt (e i) + t ^ (k / 2) * Real.sqrt (v i)))
    (hsecond : ∀ i ∈ bands, (∫ x, (((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i) x) ^ 2 ∂P) ≤
      C * s ^ 2 * (t ^ (-(k + 4)) * e i + t ^ (-(k + 3)) * v i))
    (hbadNorm : ∀ i ∈ bands,
      eLpNorm ((Bad i).indicator ((Small i).indicator (T i))) 2 P ≤
        ENNReal.ofReal (B * Real.exp (-c * K))) :
    MemLp (fun x ↦ ∑ i ∈ bands, (Small i).indicator (T i) x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, (Small i).indicator (T i) x) 2 P ≤
        ENNReal.ofReal (((2 * (8 : ℝ) ^ (3 / 4 : ℝ) + 2 * Real.sqrt 8) * Real.sqrt C * Real.sqrt E) *
          (t ^ (k / 8) * (s / t) ^ (k / (4 * (3 * k + 4)))) +
          (bands.card : ℝ) * (B * Real.exp (-c * K))) := by
  have hg := birthBand_small_traffic_interpolated_level_norm P bands
    (fun i ↦ ((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i)) hgood e v he hv
    ht ht1 hs hC hE1 hk hNs hE hV hfirst hsecond
  exact finite_sceneEvent_traffic_memLp_two_of_good_bad_norm_bounds P bands Small Bad T
    hg.1 hbad (by positivity) (by positivity) hg.2 hbadNorm

/-- The actual rankZero finite band sum retains its true scene-small event,
its own count-good energy estimates and its original count-tail norm. -/
theorem birthBand_rankZero_sceneEvent_traffic_level_norm
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (Small Bad : ι → Set Ω) (T : ι → Ω → ℝ)
    (hgood : ∀ i ∈ bands, MemLp (((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i)) 2 P)
    (hbad : ∀ i ∈ bands, MemLp ((Bad i).indicator ((Small i).indicator (T i))) 2 P)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i)
    {E t s C B c K : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s) (hC : 0 ≤ C)
    (hE1 : 1 ≤ E) (hB : 0 ≤ B)
    (hNs : (bands.card : ℝ) * s = 8 * t)
    (hV : (∑ i ∈ bands, v i) ≤ E)
    (hfirst : ∀ i ∈ bands, (∫ x, (((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i) x) ^ 2 ∂P) ≤
      (C * s ^ (3 / 2 : ℝ)) * Real.sqrt (v i))
    (hsecond : ∀ i ∈ bands, (∫ x, (((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i) x) ^ 2 ∂P) ≤
      C * s ^ 2 * (t ^ (-3 : ℝ) * v i))
    (hbadNorm : ∀ i ∈ bands,
      eLpNorm ((Bad i).indicator ((Small i).indicator (T i))) 2 P ≤
        ENNReal.ofReal (B * Real.exp (-c * K))) :
    MemLp (fun x ↦ ∑ i ∈ bands, (Small i).indicator (T i) x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, (Small i).indicator (T i) x) 2 P ≤
        ENNReal.ofReal ((((8 : ℝ) ^ (3 / 4 : ℝ) + 2 * Real.sqrt 8) * Real.sqrt C * Real.sqrt E) *
          (t ^ (3 / 8 : ℝ) * (s / t) ^ (3 / 28 : ℝ)) +
          (bands.card : ℝ) * (B * Real.exp (-c * K))) := by
  have hg := birthBand_rankZero_traffic_interpolated_level_norm P bands
    (fun i ↦ ((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i)) hgood v hv
    ht ht1 hs hC hE1 hNs hV hfirst hsecond
  exact finite_sceneEvent_traffic_memLp_two_of_good_bad_norm_bounds P bands Small Bad T
    hg.1 hbad (by positivity) (by positivity) hg.2 hbadNorm

end OTSelector.Probability

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Tactic.NormNum
import OTSelector.MeasureTheory.Lp.BandWidthEnergySum
import OTSelector.MeasureTheory.Lp.FiniteGoodBadSum

/-!
# Probability.RegularBirthSceneEventLevelNorm

**Conditions:** Finite band traffic has the displayed good/bad L2 memberships, good energy budget, band-count scale bound and bad exponential norm bound.

**Objects:** The literal scene-small regular-birth level traffic and its square-root-scale energy plus full band-count tail.

**Proof detail:** Apply the common finite-band Cauchy–Schwarz/Minkowski energy estimate to the good indicator, then add the bad indicators in L2, retaining their actual number of bands.

**Sources:** [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=214), Section 7A, Theorem 7.14, p. 199 (Minkowski); [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=211), Section 7A, Theorem 7.9, pp. 196–197 (Hölder); Theorem 7.10, p. 197 (finite-measure Lq to Lp); [OTSelector project, Regular focal birth traffic band summation](main.tex#eq:focal-traffic-birth-sum), main.tex label eq:focal-traffic-birth-sum, line 9915.

Source relation (composition): The cited primary sections give the mathematical principles used here. The exact source statement, endpoint convention, measure generality and finite encoding are local corollaries or Lean adapters rather than a claim that the book states the Lean theorem verbatim.
-/


/-! The literal scene-small regular-birth band traffic keeps the same original
momentum budget and adds its original full-input count tail in L2. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- The regular-birth level has its physical sqrt(s) energy gain plus the
literal number-of-bands original exponential count-tail contribution. -/
theorem regularBirth_sceneEvent_traffic_level_norm
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (Small Bad : ι → Set Ω) (T : ι → Ω → ℝ)
    (hgood : ∀ i ∈ bands, MemLp (((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i)) 2 P)
    (hbad : ∀ i ∈ bands, MemLp ((Bad i).indicator ((Small i).indicator (T i))) 2 P)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i)
    {E C s H B c K : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hNs : (bands.card : ℝ) * s ≤ H)
    (hV : (∑ i ∈ bands, v i) ≤ E)
    (hmean : ∀ i ∈ bands,
      (∫ x, (((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i) x) ^ 2 ∂P) ≤ C * s ^ 2 * v i)
    (hbadNorm : ∀ i ∈ bands,
      eLpNorm ((Bad i).indicator ((Small i).indicator (T i))) 2 P ≤
        ENNReal.ofReal (B * Real.exp (-c * K))) :
    MemLp (fun x ↦ ∑ i ∈ bands, (Small i).indicator (T i) x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, (Small i).indicator (T i) x) 2 P ≤
        ENNReal.ofReal (Real.sqrt H * Real.sqrt C * Real.sqrt E * Real.sqrt s +
          (bands.card : ℝ) * (B * Real.exp (-c * K))) := by
  have hg := regularBirth_finiteBand_traffic_memLp_two_of_momentum_budget P bands
    (fun i ↦ ((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i)) hgood v hv hs hC hNs hV hmean
  exact finite_sceneEvent_traffic_memLp_two_of_good_bad_norm_bounds P bands Small Bad T
    hg.1 hbad (by positivity) (by positivity) hg.2 hbadNorm

end OTSelector.Probability

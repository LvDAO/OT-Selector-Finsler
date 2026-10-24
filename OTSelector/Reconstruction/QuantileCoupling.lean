import Mathlib.Probability.CDF
import OTSelector.Reconstruction.OrderCouplingConstruction

/-!
# Quantile machinery and the quantile (co-monotone) coupling

The Mathlib `ProbabilityTheory.cdf` provides the cumulative distribution function of
a real measure as a `StieltjesFunction` (monotone and right continuous, with limits
`0` at `-∞` and `1` at `+∞`).  This file builds the generalized inverse (quantile)
from it and the resulting order coupling.

* `unitIntervalLaw`: the uniform law on `(0, 1)`;
* `quantile μ u := sInf {x | u ≤ cdf μ x}`: the generalized inverse of the cdf;
* `quantile_le_of_le_cdf`, `cdf_lt_of_lt_quantile`: elementary inverse relations;
* `quantile_monoOn`: the quantile is monotone on `(0, 1)`;
* `aemeasurable_quantile`: the quantile is a.e. measurable for the uniform law;
* `quantile_le_quantile_of_cdf_le`: stochastic dominance (lower cdf) implies the
  order inequality of the quantiles;
* `exists_orderCoupling_of_quantileMap`: the quantile coupling: if the quantiles
  push the uniform law forward to the two laws, then the joint law of the two
  quantiles is a coupling supported on the order relation.

The only remaining step for the unconditional general order coupling is the
pushforward identity `unitIntervalLaw.map (quantile μ) = μ` (the quantile is the
cdf inverse in distribution).  Its right-continuity ingredient is available in
the `StieltjesFunction` structure as `right_continuous`, and it is taken as an
explicit hypothesis below.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

/-- The uniform law on the open unit interval. -/
def unitIntervalLaw : Measure ℝ := volume.restrict (Set.Ioo (0:ℝ) 1)

instance : IsProbabilityMeasure unitIntervalLaw := by
  constructor
  rw [unitIntervalLaw, Measure.restrict_apply_univ]
  simp

/-- The generalized inverse (quantile) of the cumulative distribution function:
the least point at which the cdf reaches the level `u`. -/
noncomputable def quantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | u ≤ cdf μ x}

/-- For levels in `(0, 1)` the defining set of the quantile is bounded below. -/
theorem quantile_bddBelow (μ : Measure ℝ) {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    BddBelow {x : ℝ | u ≤ cdf μ x} := by
  obtain ⟨x0, hx0⟩ : ∃ x0, cdf μ x0 < u :=
    ((tendsto_cdf_atBot μ).eventually (isOpen_Iio.mem_nhds hu.1)).exists
  refine ⟨x0, ?_⟩
  intro x hx
  by_contra hcon
  have hlt : x < x0 := not_le.mp hcon
  have hle : cdf μ x ≤ cdf μ x0 := monotone_cdf μ hlt.le
  exact (not_lt_of_ge (le_trans hx hle)) hx0

/-- For levels in `(0, 1)` the defining set of the quantile is nonempty. -/
theorem quantile_nonempty (μ : Measure ℝ) {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    {x : ℝ | u ≤ cdf μ x}.Nonempty := by
  obtain ⟨x, hx⟩ : ∃ x, u < cdf μ x :=
    ((tendsto_cdf_atTop μ).eventually (isOpen_Ioi.mem_nhds hu.2)).exists
  exact ⟨x, le_of_lt hx⟩

/-- The quantile is a lower bound of the level set: the easy inverse relation. -/
theorem quantile_le_of_le_cdf (μ : Measure ℝ) {u x : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) (hx : u ≤ cdf μ x) : quantile μ u ≤ x :=
  csInf_le (quantile_bddBelow μ hu) hx

/-- Points strictly below the quantile have cdf strictly below the level. -/
theorem cdf_lt_of_lt_quantile (μ : Measure ℝ) {u x : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) (hx : x < quantile μ u) : cdf μ x < u := by
  by_contra hcon
  have hcon' : u ≤ cdf μ x := le_of_not_gt hcon
  have h := quantile_le_of_le_cdf μ hu hcon'
  linarith

/-- The quantile is monotone on the open unit interval. -/
theorem quantile_monoOn (μ : Measure ℝ) :
    MonotoneOn (quantile μ) (Set.Ioo (0:ℝ) 1) := by
  intro u hu v hv huv
  have hsub : {x : ℝ | v ≤ cdf μ x} ⊆ {x : ℝ | u ≤ cdf μ x} :=
    fun x hx => le_trans huv hx
  exact csInf_le_csInf (quantile_bddBelow μ hu) (quantile_nonempty μ hv) hsub

/-- The quantile is a.e. measurable for the uniform law. -/
theorem aemeasurable_quantile (μ : Measure ℝ) :
    AEMeasurable (quantile μ) unitIntervalLaw :=
  aemeasurable_restrict_of_monotoneOn (μ := volume) measurableSet_Ioo
    (quantile_monoOn μ)

/-- Stochastic dominance (the source cdf dominates the target cdf pointwise) gives
the pointwise order of the quantiles on the open unit interval. -/
theorem quantile_le_quantile_of_cdf_le {μ ν : Measure ℝ}
    (hdom : ∀ t, cdf ν t ≤ cdf μ t) {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    quantile μ u ≤ quantile ν u := by
  have hsub : {x : ℝ | u ≤ cdf ν x} ⊆ {x : ℝ | u ≤ cdf μ x} :=
    fun x hx => le_trans hx (hdom x)
  exact csInf_le_csInf (quantile_bddBelow μ hu) (quantile_nonempty ν hu) hsub

/-- The quantile coupling: under stochastic dominance, if the quantiles push the
uniform law on `(0, 1)` forward to the two laws, then the joint law of the two
quantiles is a coupling supported on the order relation. -/
theorem exists_orderCoupling_of_quantileMap
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ t, cdf ν t ≤ cdf μ t)
    (hmapμ : unitIntervalLaw.map (quantile μ) = μ)
    (hmapν : unitIntervalLaw.map (quantile ν) = ν) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧ Vlasov.IsCoupling π μ ν ∧
      ∀ᵐ p ∂π, p.1 ≤ p.2 := by
  have hμ_ae : AEMeasurable (quantile μ) unitIntervalLaw := aemeasurable_quantile μ
  have hν_ae : AEMeasurable (quantile ν) unitIntervalLaw := aemeasurable_quantile ν
  have hpair : AEMeasurable (fun u : ℝ => (quantile μ u, quantile ν u))
      unitIntervalLaw :=
    hμ_ae.prodMk hν_ae
  refine ⟨unitIntervalLaw.map (fun u => (quantile μ u, quantile ν u)),
    Measure.isProbabilityMeasure_map hpair, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [AEMeasurable.map_map_of_aemeasurable
        (f := fun u : ℝ => (quantile μ u, quantile ν u)) (g := Prod.fst)
        measurable_fst.aemeasurable hpair]
      exact hmapμ
    · rw [AEMeasurable.map_map_of_aemeasurable
        (f := fun u : ℝ => (quantile μ u, quantile ν u)) (g := Prod.snd)
        measurable_snd.aemeasurable hpair]
      exact hmapν
  · rw [ae_iff]
    rw [show {a : ℝ × ℝ | ¬ a.1 ≤ a.2} = {a : ℝ × ℝ | a.1 ≤ a.2}ᶜ from rfl]
    rw [Measure.map_apply_of_aemeasurable hpair
      (measurableSet_le measurable_fst measurable_snd).compl]
    change unitIntervalLaw {u : ℝ | ¬ quantile μ u ≤ quantile ν u} = 0
    have hsub : {u : ℝ | ¬ quantile μ u ≤ quantile ν u} ⊆
        (Set.Ioo (0:ℝ) 1)ᶜ := by
      intro u hu hmem
      exact hu (quantile_le_quantile_of_cdf_le hdom hmem)
    exact measure_mono_null hsub (by simp [unitIntervalLaw])

end OTSelector.Reconstruction

end

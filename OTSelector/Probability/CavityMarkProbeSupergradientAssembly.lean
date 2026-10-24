import OTSelector.Probability.CavityProbeReadoutBridge
import OTSelector.Probability.ParameterizedAffineTilts

/-!
# Constructed mark-probe supergradients with the vanishing readout

`CavityProbeReadoutBridge` proves the readout `qpos n - qneg n → 0` for an
*explicitly given* allocation family and specializes the opposite-tilt
supergradient inequalities to the mark probe.  This module closes the remaining
construction gap: the allocation families are produced from the actual cavity
optimizer construction `exists_jointlyMeasurable_opposite_semidiscrete_optima_for_tilts`,
and the tilted atomlessness inputs are reduced to a countable exceptional set of
probe tilts.

## Main results

* `cavityMarkProbeBadTiltsAt` / `cavityMarkProbeBadTilts`: the level-wise and
  uniform exceptional sets of tilts at which the tilted pairwise cost
  differences may fail to be atomless on the source law;
* `countable_cavityMarkProbeBadTiltsAt` / `countable_cavityMarkProbeBadTilts`:
  their countability, from base atomlessness, continuity of `k` and
  measurability/boundedness of `gm`;
* `exists_cavityMarkProbe_allocation_family`: construction of measurable
  allocation families `Aplus`/`Amin` that are a.e. optimal for the plus- and
  minus-tilt mark-probe costs;
* `cavityMarkProbe_supergradient_pair_of_family`: the level-wise supergradient
  inequalities for the constructed families, via
  `markProbe_opposite_tilt_supergradient_pair`;
* `exists_cavityMarkProbe_diagonal_allocations_of_good`: the diagonal of the
  level-wise construction, giving measurable families a.e. optimal at `t n`
  and `-t n`;
* `cavityMarkProbe_supergradients_with_tendsto` / `exists_cavityMarkProbe_supergradients_with_tendsto`:
  the `hsup` package for the physical pressure: plus/minus supergradient
  inequalities with `qpos`/`qneg` defined as the cavity mark-probe allocation
  costs, the definitional identifications, the constructed families'
  measurability and a.e. optimality, and `qpos n - qneg n → 0`.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped BigOperators ENNReal NNReal CompactlySupported

noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]

section Assembly

variable [TopologicalSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [MetricSpace B] [CompactSpace B] [BorelSpace B] [SecondCountableTopology B]
  [StandardBorelSpace ((ι → ℝ) × A)]
  (base : (ι → ℝ) × B)

open PointProcess PointProcess.LocalConfiguration

local instance markProbeBorelTarget : StandardBorelSpace ((ι → ℝ) × B) := inferInstance
local instance markProbeConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance markProbeConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance markProbeConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance markProbePlanPolish :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace
local instance markProbeCloudPolish : PolishSpace (LocalFiniteMeasure ((ι → ℝ) × B)) :=
  LocalFiniteMeasure.instPolishSpace

/-- The plus/minus tilt cost of the mark probe at a fixed target cloud and
source point. -/
def cavityMarkProbeTiltedCost (k : A → B → (ι → ℝ) → ℝ) (gm : A → B → ℝ)
    (v : Fin (m + 1) → ((ι → ℝ) × B)) (u : ℝ)
    (s : (ι → ℝ) × A) (j : Fin (m + 1)) : ℝ :=
  cavitySpatialDifferenceCost k s (v j) + u * gm s.2 ((v j).2)

/-- **Level-wise bad tilts.**  A tilt `u` is bad at level `m` when on a
positive-measure set of target clouds some tilted pairwise cost difference of
the mark probe fails to have null-singleton image under the source law. -/
def cavityMarkProbeBadTiltsAt (m : ℕ)
    (μ : Measure ((ι → ℝ) × A)) (ν : Measure ((ι → ℝ) × B))
    (k : A → B → (ι → ℝ) → ℝ) (gm : A → B → ℝ) : Set ℝ :=
  {u | ¬ ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)),
    ∀ j l, j ≠ l → NullSingletonClass
      ((μ).map (fun s ↦
        cavityMarkProbeTiltedCost k gm v u s j -
          cavityMarkProbeTiltedCost k gm v u s l))}

/-- **The uniform exceptional tilt set.**  Union over the levels of the
level-wise bad tilt sets. -/
def cavityMarkProbeBadTilts (m : ℕ → ℕ) (μ : ℕ → Measure ((ι → ℝ) × A))
    (ν : ℕ → Measure ((ι → ℝ) × B)) (k : A → B → (ι → ℝ) → ℝ)
    (gm : A → B → ℝ) : Set ℝ :=
  ⋃ n, cavityMarkProbeBadTiltsAt (m n) (μ n) (ν n) k gm

set_option maxHeartbeats 1200000 in
/-- **Level-wise bad tilts are countable.**  Base atomlessness, continuity of
`k` and measurability of `gm` make the parameterized cavity tilt countability
theorem applicable. -/
theorem countable_cavityMarkProbeBadTiltsAt (m : ℕ)
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (k : A → B → (ι → ℝ) → ℝ) (gm : A → B → ℝ)
    (hgm : Measurable (Function.uncurry gm))
    (hcost : Continuous (Function.uncurry (cavitySpatialDifferenceCost k)))
    (hatom : ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ).map (fun s ↦ cavitySpatialDifferenceCost k s (v j) -
          cavitySpatialDifferenceCost k s (v l)))) :
    (cavityMarkProbeBadTiltsAt m μ ν k gm).Countable := by
  let V := Fin (m + 1) → ((ι → ℝ) × B)
  let ρ : Measure V := Measure.pi (fun _ : Fin (m + 1) ↦ ν)
  let c : Fin (m + 1) → V → ((ι → ℝ) × A) → ℝ :=
    fun j v s ↦ cavitySpatialDifferenceCost k s (v j)
  let g : Fin (m + 1) → V → ((ι → ℝ) × A) → ℝ :=
    fun j v s ↦ gm s.2 ((v j).2)
  have hc (j : Fin (m + 1)) : Measurable (Function.uncurry (c j)) := by
    have hpair : Measurable (fun z : V × ((ι → ℝ) × A) ↦ (z.2, z.1 j)) :=
      measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst)
    exact hcost.measurable.comp hpair
  have hg (j : Fin (m + 1)) : Measurable (Function.uncurry (g j)) := by
    have hpair : Measurable (fun z : V × ((ι → ℝ) × A) ↦
        (z.2.2, (z.1 j).2)) :=
      measurable_snd.snd.prodMk ((measurable_pi_apply j).comp measurable_fst).snd
    exact hgm.comp hpair
  have hatom' : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass ((μ).map (fun s ↦ c j v s - c l v s)) := by
    simpa only [ρ, c] using hatom
  have h := countable_bad_parameterized_cavity_tilts (μ := μ) (ρ := ρ)
    (ι := Fin (m + 1)) c g hc hg hatom'
  refine h.mono ?_
  intro u hu
  intro hgood
  apply hu
  filter_upwards [hgood] with v hv j l hjl
  have hfun : (fun s ↦ c j v s + u * g j v s - (c l v s + u * g l v s)) =
      (fun s ↦ cavityMarkProbeTiltedCost k gm v u s j -
        cavityMarkProbeTiltedCost k gm v u s l) := by
    funext s
    simp only [c, g, cavityMarkProbeTiltedCost]
  rw [← hfun]
  exact hv j l hjl

/-- **The uniform exceptional tilt set is countable.** -/
theorem countable_cavityMarkProbeBadTilts
    (m : ℕ → ℕ) (μ : ℕ → Measure ((ι → ℝ) × A))
    (ν : ℕ → Measure ((ι → ℝ) × B)) (k : A → B → (ι → ℝ) → ℝ)
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (hcost : Continuous (Function.uncurry (cavitySpatialDifferenceCost k)))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (hatom : ∀ n, ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ n).map (fun s ↦ cavitySpatialDifferenceCost k s (v j) -
          cavitySpatialDifferenceCost k s (v l)))) :
    (cavityMarkProbeBadTilts m μ ν k gm).Countable := by
  unfold cavityMarkProbeBadTilts
  exact Set.countable_iUnion fun n ↦
    countable_cavityMarkProbeBadTiltsAt (m n) (μ n) (ν n) k gm hgm hcost (hatom n)

set_option maxHeartbeats 2400000 in
/-- **Construction of the mark-probe allocation families.**  Base and tilted
atomlessness, joint integrability of the cost and the bounded measurable probe
produce measurable allocation families `Aplus`/`Amin` that are almost surely
optimal for the plus- and minus-tilt costs. -/
theorem exists_cavityMarkProbe_allocation_family
    (m : ℕ) (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (k : A → B → (ι → ℝ) → ℝ) (gm : A → B → ℝ)
    (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ≥0) (hgmb : ∀ a b, |gm a b| ≤ (Cg : ℝ))
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (hcost : Continuous (Function.uncurry (cavitySpatialDifferenceCost k)))
    (hcij : ∀ j, Integrable
      (fun z : (Fin (m + 1) → ((ι → ℝ) × B)) × ((ι → ℝ) × A) ↦
        cavitySpatialDifferenceCost k z.2 (z.1 j))
      ((Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod μ))
    (hatom : ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ).map (fun s ↦ cavitySpatialDifferenceCost k s (v j) -
          cavitySpatialDifferenceCost k s (v l))))
    (htatom : ∀ n, ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ).map (fun s ↦
          (cavitySpatialDifferenceCost k s (v j) + t n * gm s.2 ((v j).2)) -
          (cavitySpatialDifferenceCost k s (v l) + t n * gm s.2 ((v l).2)))))
    (htatomneg : ∀ n, ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ).map (fun s ↦
          (cavitySpatialDifferenceCost k s (v j) + (-t n) * gm s.2 ((v j).2)) -
          (cavitySpatialDifferenceCost k s (v l) + (-t n) * gm s.2 ((v l).2))))) :
    ∃ Aplus Amin : ℕ → ((Fin (m + 1) → ((ι → ℝ) × B)) ×
        (Fin (m + 1) → ℝ)) × ((ι → ℝ) × A) → Fin (m + 1) → ℝ,
      (∀ n j, Measurable (fun z ↦ Aplus n z j)) ∧
      (∀ n j, Measurable (fun z ↦ Amin n z j)) ∧
      ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m),
        (∀ n, IsOptimalSemidiscreteAllocation μ z.2
          (fun s j ↦
            cavitySpatialDifferenceCost k s (z.1 j) + t n * gm s.2 ((z.1 j).2))
          (fun s ↦ Aplus n (z, s))) ∧
        (∀ n, IsOptimalSemidiscreteAllocation μ z.2
          (fun s j ↦
            cavitySpatialDifferenceCost k s (z.1 j) + (-t n) * gm s.2 ((z.1 j).2))
          (fun s ↦ Amin n (z, s))) := by
  let V := Fin (m + 1) → ((ι → ℝ) × B)
  let ρ : Measure V := Measure.pi (fun _ : Fin (m + 1) ↦ ν)
  let c : V → Fin (m + 1) → ((ι → ℝ) × A) → ℝ :=
    fun v j s ↦ cavitySpatialDifferenceCost k s (v j)
  let g : V → Fin (m + 1) → ((ι → ℝ) × A) → ℝ :=
    fun v j s ↦ gm s.2 ((v j).2)
  have hc (j : Fin (m + 1)) : Measurable (fun z : V × ((ι → ℝ) × A) ↦ c z.1 j z.2) := by
    have hpair : Measurable (fun z : V × ((ι → ℝ) × A) ↦ (z.2, z.1 j)) :=
      measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst)
    exact hcost.measurable.comp hpair
  have hg (j : Fin (m + 1)) :
      Measurable (fun z : V × ((ι → ℝ) × A) ↦ g z.1 j z.2) := by
    have hpair : Measurable (fun z : V × ((ι → ℝ) × A) ↦ (z.2.2, (z.1 j).2)) :=
      measurable_snd.snd.prodMk ((measurable_pi_apply j).comp measurable_fst).snd
    exact hgm.comp hpair
  have hci : ∀ᵐ v ∂ρ, ∀ j, Integrable (c v j) μ := by
    apply ae_all_iff.mpr
    intro j
    simpa only [ρ, c] using (hcij j).prod_right_ae
  have hbound : ∀ v s j, |g v j s| ≤ (Cg : ℝ) := fun v s j ↦ hgmb s.2 ((v j).2)
  obtain ⟨A₀, Aplus, Amin, hA₀, hAplus, hAmin, hopt⟩ :=
    exists_jointlyMeasurable_opposite_semidiscrete_optima_for_tilts
      (m := m) (S := ((ι → ℝ) × A)) (V := V) μ ρ c g hc hci hg
      hatom Cg hbound t htpos htatom htatomneg
  refine ⟨Aplus, Amin, hAplus, hAmin, ?_⟩
  filter_upwards [hopt] with z hz
  exact ⟨fun n ↦ (hz.2 n).1, fun n ↦ (hz.2 n).2.1⟩

/-- Avoiding the exceptional set gives the level-wise tilted atomlessness. -/
theorem ae_atomless_of_notMem_cavityMarkProbeBadTilts
    (m : ℕ → ℕ) (μ : ℕ → Measure ((ι → ℝ) × A))
    (ν : ℕ → Measure ((ι → ℝ) × B)) (k : A → B → (ι → ℝ) → ℝ)
    (gm : A → B → ℝ) [∀ n, IsProbabilityMeasure (μ n)]
    [∀ n, IsProbabilityMeasure (ν n)] {u : ℝ}
    (hu : u ∉ cavityMarkProbeBadTilts m μ ν k gm) (n : ℕ) :
    ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ n).map (fun s ↦
          cavityMarkProbeTiltedCost k gm v u s j -
            cavityMarkProbeTiltedCost k gm v u s l)) := by
  have hn : u ∉ cavityMarkProbeBadTiltsAt (m n) (μ n) (ν n) k gm :=
    fun hmem ↦ hu (Set.mem_iUnion.mpr ⟨n, hmem⟩)
  exact Classical.not_not.mp hn

set_option maxHeartbeats 2400000 in
/-- **Allocation construction from good tilts.**  This is
`exists_cavityMarkProbe_allocation_family` with the tilted atomlessness inputs
replaced by the countable-exceptional-set condition. -/
theorem exists_cavityMarkProbe_allocation_family_of_good
    (m : ℕ → ℕ) (μ : ℕ → Measure ((ι → ℝ) × A))
    (ν : ℕ → Measure ((ι → ℝ) × B)) (k : A → B → (ι → ℝ) → ℝ)
    (gm : A → B → ℝ) [∀ n, IsProbabilityMeasure (μ n)]
    [∀ n, IsProbabilityMeasure (ν n)]
    (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ≥0) (hgmb : ∀ a b, |gm a b| ≤ (Cg : ℝ))
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (hcost : Continuous (Function.uncurry (cavitySpatialDifferenceCost k)))
    (hcij : ∀ n j, Integrable
      (fun z : (Fin (m n + 1) → ((ι → ℝ) × B)) × ((ι → ℝ) × A) ↦
        cavitySpatialDifferenceCost k z.2 (z.1 j))
      ((Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod (μ n)))
    (hatom : ∀ n, ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ n).map (fun s ↦ cavitySpatialDifferenceCost k s (v j) -
          cavitySpatialDifferenceCost k s (v l))))
    (htgood : ∀ j, t j ∉ cavityMarkProbeBadTilts m μ ν k gm)
    (htgoodneg : ∀ j, -t j ∉ cavityMarkProbeBadTilts m μ ν k gm) :
    ∀ n, ∃ Aplus Amin : ℕ →
        ((Fin (m n + 1) → ((ι → ℝ) × B)) × (Fin (m n + 1) → ℝ)) ×
          ((ι → ℝ) × A) → Fin (m n + 1) → ℝ,
      (∀ i j, Measurable (fun z ↦ Aplus i z j)) ∧
      (∀ i j, Measurable (fun z ↦ Amin i z j)) ∧
      ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod (dirichletOne (m n)),
        (∀ i, IsOptimalSemidiscreteAllocation (μ n) z.2
          (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) +
            t i * gm s.2 ((z.1 j).2)) (fun s ↦ Aplus i (z, s))) ∧
        (∀ i, IsOptimalSemidiscreteAllocation (μ n) z.2
          (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) +
            (-t i) * gm s.2 ((z.1 j).2)) (fun s ↦ Amin i (z, s))) := by
  intro n
  refine exists_cavityMarkProbe_allocation_family (m := m n) (μ := μ n) (ν := ν n)
    k gm hgm Cg hgmb t htpos hcost (hcij n) (hatom n) ?_ ?_
  · intro j
    exact ae_atomless_of_notMem_cavityMarkProbeBadTilts m μ ν k gm (htgood j) n
  · intro j
    exact ae_atomless_of_notMem_cavityMarkProbeBadTilts m μ ν k gm (htgoodneg j) n

set_option maxHeartbeats 2400000 in
/-- **Level-wise supergradient inequalities for an allocation family.**  For a
fixed cavity level, a family that is a.e. optimal at every tilt of the sequence
`t` produces the opposite-tilt supergradient inequalities, via
`markProbe_opposite_tilt_supergradient_pair`. -/
theorem cavityMarkProbe_supergradient_pair_of_family
    (m : ℕ) (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (k : A → B → (ι → ℝ) → ℝ)
    (hcost : Continuous (Function.uncurry (cavitySpatialDifferenceCost k)))
    (hcij : ∀ j, Integrable
      (fun z : (Fin (m + 1) → ((ι → ℝ) × B)) × ((ι → ℝ) × A) ↦
        cavitySpatialDifferenceCost k z.2 (z.1 j))
      ((Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod μ))
    (hatom : ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ).map (fun s ↦ cavitySpatialDifferenceCost k s (v j) -
          cavitySpatialDifferenceCost k s (v l))))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ≥0) (hgmb : ∀ a b, |gm a b| ≤ (Cg : ℝ))
    (t : ℕ → ℝ)
    (Aplus Amin : ℕ → ((Fin (m + 1) → ((ι → ℝ) × B)) ×
        (Fin (m + 1) → ℝ)) × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hAplusm : ∀ n j, Measurable (fun z ↦ Aplus n z j))
    (hAminm : ∀ n j, Measurable (fun z ↦ Amin n z j))
    (hplusopt : ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod
        (dirichletOne m),
      IsOptimalSemidiscreteAllocation μ z.2
        (fun s j ↦
          cavitySpatialDifferenceCost k s (z.1 j) + t n * gm s.2 ((z.1 j).2))
        (fun s ↦ Aplus n (z, s)))
    (hminusopt : ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod
        (dirichletOne m),
      IsOptimalSemidiscreteAllocation μ z.2
        (fun s j ↦
          cavitySpatialDifferenceCost k s (z.1 j) + (-t n) * gm s.2 ((z.1 j).2))
        (fun s ↦ Amin n (z, s))) :
    (∀ n u, cavityMarkProbePressure m μ ν k gm u ≤
      cavityMarkProbePressure m μ ν k gm (t n) +
        cavityMarkProbeAllocationCost μ gm ν (Aplus n) * (u - t n)) ∧
    (∀ n u, cavityMarkProbePressure m μ ν k gm u ≤
      cavityMarkProbePressure m μ ν k gm (-(t n)) +
        cavityMarkProbeAllocationCost μ gm ν (Amin n) * (u + t n)) := by
  constructor
  · intro n u
    have h := markProbe_opposite_tilt_supergradient_pair (m := m) (μ := μ) (ν := ν)
      k hcost hcij hatom gm hgm Cg hgmb (fun _ ↦ t n) (Aplus n) (Amin n)
      (hAplusm n) (hAminm n) (fun _ ↦ hplusopt n) (fun _ ↦ hminusopt n)
    exact h.1 0 u
  · intro n u
    have h := markProbe_opposite_tilt_supergradient_pair (m := m) (μ := μ) (ν := ν)
      k hcost hcij hatom gm hgm Cg hgmb (fun _ ↦ t n) (Aplus n) (Amin n)
      (hAplusm n) (hAminm n) (fun _ ↦ hplusopt n) (fun _ ↦ hminusopt n)
    exact h.2 0 u

set_option maxHeartbeats 2400000 in
/-- **Diagonal allocation families from good tilts.**  Choosing the level-`n`
entry of the level-`n` construction gives measurable families that are a.e.
optimal at `t n` and `-t n`. -/
theorem exists_cavityMarkProbe_diagonal_allocations_of_good
    (m : ℕ → ℕ) (μ : ℕ → Measure ((ι → ℝ) × A))
    (ν : ℕ → Measure ((ι → ℝ) × B)) (k : A → B → (ι → ℝ) → ℝ)
    (gm : A → B → ℝ) [∀ n, IsProbabilityMeasure (μ n)]
    [∀ n, IsProbabilityMeasure (ν n)]
    (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ≥0) (hgmb : ∀ a b, |gm a b| ≤ (Cg : ℝ))
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (hcost : Continuous (Function.uncurry (cavitySpatialDifferenceCost k)))
    (hcij : ∀ n j, Integrable
      (fun z : (Fin (m n + 1) → ((ι → ℝ) × B)) × ((ι → ℝ) × A) ↦
        cavitySpatialDifferenceCost k z.2 (z.1 j))
      ((Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod (μ n)))
    (hatom : ∀ n, ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ n).map (fun s ↦ cavitySpatialDifferenceCost k s (v j) -
          cavitySpatialDifferenceCost k s (v l))))
    (htgood : ∀ j, t j ∉ cavityMarkProbeBadTilts m μ ν k gm)
    (htgoodneg : ∀ j, -t j ∉ cavityMarkProbeBadTilts m μ ν k gm) :
    ∃ Aplus Amin : ∀ n, ((Fin (m n + 1) → ((ι → ℝ) × B)) ×
        (Fin (m n + 1) → ℝ)) × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ,
      (∀ n j, Measurable (fun z ↦ Aplus n z j)) ∧
      (∀ n j, Measurable (fun z ↦ Amin n z j)) ∧
      ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod
          (dirichletOne (m n)),
        IsOptimalSemidiscreteAllocation (μ n) z.2
          (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) +
            t n * gm s.2 ((z.1 j).2)) (fun s ↦ Aplus n (z, s)) ∧
        IsOptimalSemidiscreteAllocation (μ n) z.2
          (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) +
            (-t n) * gm s.2 ((z.1 j).2)) (fun s ↦ Amin n (z, s)) := by
  choose AplusF AminF hprops using
    exists_cavityMarkProbe_allocation_family_of_good m μ ν k gm hgm Cg hgmb t htpos
      hcost hcij hatom htgood htgoodneg
  refine ⟨fun n ↦ AplusF n n, fun n ↦ AminF n n, ?_, ?_, ?_⟩
  · intro n j
    exact (hprops n).1 n j
  · intro n j
    exact (hprops n).2.1 n j
  · intro n
    filter_upwards [(hprops n).2.2] with z hz
    exact ⟨hz.1 n, hz.2 n⟩

set_option maxHeartbeats 4000000 in
/-- **Constructed mark-probe supergradients with vanishing readout.**  For
explicit allocation families that are a.e. optimal at `±t n` (as produced by
`exists_cavityMarkProbe_diagonal_allocations_of_good`) and environment
allocations linked to them, the `hsup` package holds for the physical pressure
`Pphys`: the plus/minus supergradient inequalities with `qpos`/`qneg` given by
the cavity mark-probe allocation costs, and `qpos n - qneg n → 0`. -/
theorem cavityMarkProbe_supergradients_with_tendsto
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : ℕ → Measure ((ι → ℝ) × B)) [∀ n, IsProbabilityMeasure (ν n)]
    (α : Measure A) [IsProbabilityMeasure α]
    (D : ℕ → Set (ι → ℝ))
    (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (hμsrc : ∀ n, μ n = (ENNReal.ofReal ((m n : ℝ) + 1))⁻¹ •
      ((volume.restrict (D n)).prod α))
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ) (hp : ∀ n, Measurable (p n))
    (Y : ∀ n, Ωn n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (henv : ∀ n, MeasurePreserving (fun ω ↦ (Y n ω, p n ω)) (P n)
      ((Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod (dirichletOne (m n))))
    (k : A → B → (ι → ℝ) → ℝ)
    (hcost : Continuous (Function.uncurry (cavitySpatialDifferenceCost k)))
    (hcij : ∀ n j, Integrable
      (fun z : (Fin (m n + 1) → ((ι → ℝ) × B)) × ((ι → ℝ) × A) ↦
        cavitySpatialDifferenceCost k z.2 (z.1 j))
      ((Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod (μ n)))
    (hatom : ∀ n, ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ n).map (fun s ↦ cavitySpatialDifferenceCost k s (v j) -
          cavitySpatialDifferenceCost k s (v l))))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ≥0) (hgmb : ∀ a b, |gm a b| ≤ (Cg : ℝ))
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (Aplus Amin : ∀ n, ((Fin (m n + 1) → ((ι → ℝ) × B)) ×
        (Fin (m n + 1) → ℝ)) × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hAplusm : ∀ n j, Measurable (fun z ↦ Aplus n z j))
    (hAminm : ∀ n j, Measurable (fun z ↦ Amin n z j))
    (hplusopt : ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod
        (dirichletOne (m n)),
      IsOptimalSemidiscreteAllocation (μ n) z.2
        (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) +
          t n * gm s.2 ((z.1 j).2)) (fun s ↦ Aplus n (z, s)))
    (hminusopt : ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod
        (dirichletOne (m n)),
      IsOptimalSemidiscreteAllocation (μ n) z.2
        (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) +
          (-t n) * gm s.2 ((z.1 j).2)) (fun s ↦ Amin n (z, s)))
    (aplus aminus : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hlinkplus : ∀ n (ω : Ωn n), (fun s ↦ aplus n (ω, s)) =
      fun s ↦ cavityEnvironmentAllocation (Aplus n) (p n) (Y n) ω s)
    (hlinkminus : ∀ n (ω : Ωn n), (fun s ↦ aminus n (ω, s)) =
      fun s ↦ cavityEnvironmentAllocation (Amin n) (p n) (Y n) ω s)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (hηint : Integrable η) (R : ℝ)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0)
    (φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ))
    (hφ : ∀ e, φ e = cavityMarkWindowTest η gm e)
    (hintp : ∀ n, Integrable (fun ω ↦ cavityRandomProbeDifference (μ n) gm
      (Y n) (aplus n) (aminus n) ω) (P n))
    (hints : ∀ n, Integrable (fun ω ↦ cavityRandomSceneTestDifference (μ n) (D n)
      ((m n : ℝ) + 1) η gm (Y n) (aplus n) (aminus n) ω) (P n))
    (herror : Tendsto (fun n ↦ 2 * (Cg : ℝ) * cavityRootWindowError η (D n)
      ((m n : ℝ) + 1)) atTop (𝓝 0))
    (Q : ProbabilityMeasure (CavityCountableTargetScene (A := A) base))
    (hweak : Tendsto (fun n ↦ cavityCountableSceneLawRootMeasure base (P n) (μ n)
      (p n) (hp n) (aplus n) (aminus n) (hplusm n) (hminusm n)
      (Y n) (hY n) ((m n : ℝ) + 1) (by positivity) (D n) (hD n)) atTop (𝓝 Q))
    (hplan : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      (s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) = s.1.2.1)
    (Pphys : ℕ → ℝ → ℝ)
    (hpressure_id : ∀ n u, Pphys n u =
      cavityMarkProbePressure (m n) (μ n) (ν n) k gm u) :
    ∃ qpos qneg : ℕ → ℝ,
      (∀ n, qpos n = cavityMarkProbeAllocationCost (μ n) gm (ν n) (Aplus n)) ∧
      (∀ n, qneg n = cavityMarkProbeAllocationCost (μ n) gm (ν n) (Amin n)) ∧
      (∀ᶠ n in atTop, ∀ u, Pphys n u ≤ Pphys n (t n) + qpos n * (u - t n)) ∧
      (∀ᶠ n in atTop, ∀ u, Pphys n u ≤ Pphys n (-(t n)) + qneg n * (u + t n)) ∧
      Tendsto (fun n ↦ qpos n - qneg n) atTop (𝓝 0) := by
  let qpos : ℕ → ℝ := fun n ↦ cavityMarkProbeAllocationCost (μ n) gm (ν n) (Aplus n)
  let qneg : ℕ → ℝ := fun n ↦ cavityMarkProbeAllocationCost (μ n) gm (ν n) (Amin n)
  have hsupPos : ∀ᶠ n in atTop, ∀ u, Pphys n u ≤ Pphys n (t n) + qpos n * (u - t n) := by
    filter_upwards with n u
    have h := markProbe_opposite_tilt_supergradient_pair (m := m n) (μ := μ n)
      (ν := ν n) k hcost (hcij n) (hatom n) gm hgm Cg hgmb (fun _ ↦ t n)
      (Aplus n) (Amin n) (hAplusm n) (hAminm n)
      (fun _ ↦ hplusopt n) (fun _ ↦ hminusopt n)
    have hu := h.1 0 u
    rw [hpressure_id n u, hpressure_id n (t n)]
    exact hu
  have hsupNeg : ∀ᶠ n in atTop, ∀ u, Pphys n u ≤ Pphys n (-(t n)) + qneg n * (u + t n) := by
    filter_upwards with n u
    have h := markProbe_opposite_tilt_supergradient_pair (m := m n) (μ := μ n)
      (ν := ν n) k hcost (hcij n) (hatom n) gm hgm Cg hgmb (fun _ ↦ t n)
      (Aplus n) (Amin n) (hAplusm n) (hAminm n)
      (fun _ ↦ hplusopt n) (fun _ ↦ hminusopt n)
    have hu := h.2 0 u
    rw [hpressure_id n u, hpressure_id n (-(t n))]
    exact hu
  have hdiff : Tendsto (fun n ↦ qpos n - qneg n) atTop (𝓝 0) :=
    tendsto_cavityMarkProbeAllocationCost_sub_of_weak_scene (base := base)
      (m := m) P μ ν α D hD hμsrc p hp Y hY henv Aplus Amin hAplusm hAminm
      (fun n ↦ (hplusopt n).mono fun z hz ↦ hz.1)
      (fun n ↦ (hminusopt n).mono fun z hz ↦ hz.1)
      aplus aminus hplusm hminusm hlinkplus hlinkminus gm hgm (Cg : ℝ) hgmb
      η hη Cη hηb hηint R hηsupp φ hφ hintp hints herror Q hweak hplan
  exact ⟨qpos, qneg, fun n ↦ rfl, fun n ↦ rfl, hsupPos, hsupNeg, hdiff⟩

set_option maxHeartbeats 4000000 in
/-- **Existential form of the constructed supergradient package.**  The
allocation families are not assumed: the conclusion existentially quantifies
measurable families that are a.e. optimal at `±t n` and whose induced
environment allocations are `aplus`/`aminus` (the hypothesis `hselected`).  The
existence of such families is supplied by
`exists_cavityMarkProbe_diagonal_allocations_of_good`; the link is `rfl` when
the environment allocations are *defined* from the constructed families, as in
the readout application. -/
theorem exists_cavityMarkProbe_supergradients_with_tendsto
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : ℕ → Measure ((ι → ℝ) × B)) [∀ n, IsProbabilityMeasure (ν n)]
    (α : Measure A) [IsProbabilityMeasure α]
    (D : ℕ → Set (ι → ℝ))
    (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (hμsrc : ∀ n, μ n = (ENNReal.ofReal ((m n : ℝ) + 1))⁻¹ •
      ((volume.restrict (D n)).prod α))
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ) (hp : ∀ n, Measurable (p n))
    (Y : ∀ n, Ωn n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (henv : ∀ n, MeasurePreserving (fun ω ↦ (Y n ω, p n ω)) (P n)
      ((Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod (dirichletOne (m n))))
    (k : A → B → (ι → ℝ) → ℝ)
    (hcost : Continuous (Function.uncurry (cavitySpatialDifferenceCost k)))
    (hcij : ∀ n j, Integrable
      (fun z : (Fin (m n + 1) → ((ι → ℝ) × B)) × ((ι → ℝ) × A) ↦
        cavitySpatialDifferenceCost k z.2 (z.1 j))
      ((Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod (μ n)))
    (hatom : ∀ n, ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ n).map (fun s ↦ cavitySpatialDifferenceCost k s (v j) -
          cavitySpatialDifferenceCost k s (v l))))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ≥0) (hgmb : ∀ a b, |gm a b| ≤ (Cg : ℝ))
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (aplus aminus : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hselected : ∃ Aplus Amin : ∀ n, ((Fin (m n + 1) → ((ι → ℝ) × B)) ×
        (Fin (m n + 1) → ℝ)) × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ,
      (∀ n j, Measurable (fun z ↦ Aplus n z j)) ∧
      (∀ n j, Measurable (fun z ↦ Amin n z j)) ∧
      (∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod
          (dirichletOne (m n)),
        IsOptimalSemidiscreteAllocation (μ n) z.2
          (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) +
            t n * gm s.2 ((z.1 j).2)) (fun s ↦ Aplus n (z, s)) ∧
        IsOptimalSemidiscreteAllocation (μ n) z.2
          (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) +
            (-t n) * gm s.2 ((z.1 j).2)) (fun s ↦ Amin n (z, s))) ∧
      (∀ n (ω : Ωn n), (fun s ↦ aplus n (ω, s)) =
        fun s ↦ cavityEnvironmentAllocation (Aplus n) (p n) (Y n) ω s) ∧
      (∀ n (ω : Ωn n), (fun s ↦ aminus n (ω, s)) =
        fun s ↦ cavityEnvironmentAllocation (Amin n) (p n) (Y n) ω s))
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (hηint : Integrable η) (R : ℝ)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0)
    (φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ))
    (hφ : ∀ e, φ e = cavityMarkWindowTest η gm e)
    (hintp : ∀ n, Integrable (fun ω ↦ cavityRandomProbeDifference (μ n) gm
      (Y n) (aplus n) (aminus n) ω) (P n))
    (hints : ∀ n, Integrable (fun ω ↦ cavityRandomSceneTestDifference (μ n) (D n)
      ((m n : ℝ) + 1) η gm (Y n) (aplus n) (aminus n) ω) (P n))
    (herror : Tendsto (fun n ↦ 2 * (Cg : ℝ) * cavityRootWindowError η (D n)
      ((m n : ℝ) + 1)) atTop (𝓝 0))
    (Q : ProbabilityMeasure (CavityCountableTargetScene (A := A) base))
    (hweak : Tendsto (fun n ↦ cavityCountableSceneLawRootMeasure base (P n) (μ n)
      (p n) (hp n) (aplus n) (aminus n) (hplusm n) (hminusm n)
      (Y n) (hY n) ((m n : ℝ) + 1) (by positivity) (D n) (hD n)) atTop (𝓝 Q))
    (hplan : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      (s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) = s.1.2.1)
    (Pphys : ℕ → ℝ → ℝ)
    (hpressure_id : ∀ n u, Pphys n u =
      cavityMarkProbePressure (m n) (μ n) (ν n) k gm u) :
    ∃ Aplus Amin : ∀ n, ((Fin (m n + 1) → ((ι → ℝ) × B)) ×
        (Fin (m n + 1) → ℝ)) × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ,
      (∀ n j, Measurable (fun z ↦ Aplus n z j)) ∧
      (∀ n j, Measurable (fun z ↦ Amin n z j)) ∧
      (∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod
          (dirichletOne (m n)),
        IsOptimalSemidiscreteAllocation (μ n) z.2
          (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) +
            t n * gm s.2 ((z.1 j).2)) (fun s ↦ Aplus n (z, s)) ∧
        IsOptimalSemidiscreteAllocation (μ n) z.2
          (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) +
            (-t n) * gm s.2 ((z.1 j).2)) (fun s ↦ Amin n (z, s))) ∧
      ∃ qpos qneg : ℕ → ℝ,
        (∀ n, qpos n = cavityMarkProbeAllocationCost (μ n) gm (ν n) (Aplus n)) ∧
        (∀ n, qneg n = cavityMarkProbeAllocationCost (μ n) gm (ν n) (Amin n)) ∧
        (∀ᶠ n in atTop, ∀ u, Pphys n u ≤ Pphys n (t n) + qpos n * (u - t n)) ∧
        (∀ᶠ n in atTop, ∀ u, Pphys n u ≤ Pphys n (-(t n)) + qneg n * (u + t n)) ∧
        Tendsto (fun n ↦ qpos n - qneg n) atTop (𝓝 0) := by
  obtain ⟨Aplus, Amin, hAplusm, hAminm, hopt, hlinkplus, hlinkminus⟩ := hselected
  obtain ⟨qpos, qneg, hqpos, hqneg, hpos, hneg, hdiff⟩ :=
    cavityMarkProbe_supergradients_with_tendsto (base := base) (m := m) P μ ν α D
      hD hμsrc p hp Y hY henv k hcost hcij hatom gm hgm Cg hgmb t htpos
      Aplus Amin hAplusm hAminm
      (fun n ↦ (hopt n).mono fun z hz ↦ hz.1)
      (fun n ↦ (hopt n).mono fun z hz ↦ hz.2)
      aplus aminus hplusm hminusm hlinkplus hlinkminus
      η hη Cη hηb hηint R hηsupp φ hφ hintp hints
      herror Q hweak hplan Pphys hpressure_id
  refine ⟨Aplus, Amin, hAplusm, hAminm, hopt, ?_⟩
  exact ⟨qpos, qneg, hqpos, hqneg, hpos, hneg, hdiff⟩

end Assembly

end OTSelector.Probability

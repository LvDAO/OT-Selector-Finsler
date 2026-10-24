import OTSelector.Reconstruction.FinslerSeedPieceCoefficientCore

/-!
# Countable compact windows for the original scalar pairs

Rational outer endpoints and a rational positive pair gap give countably many
compact pair regions. Actual support endpoints give the measurable exterior-mass
screens, and the original marginal laws control discarded pair mass uniformly
for every legal coupling.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- Rational outer endpoints and a positive rational separation for scalar pairs. -/
abbrev RationalScalarPairWindow :=
  {q : ℚ × ℚ × ℚ // q.1 < q.2.1 ∧ 0 < q.2.2}

namespace RationalScalarPairWindow

/-- The closed pair region associated to these rational endpoints and separation. -/
def region (q : RationalScalarPairWindow) : Set (ℝ × ℝ) :=
  (Icc (q.val.1 : ℝ) q.val.2.1 ×ˢ Icc (q.val.1 : ℝ) q.val.2.1) ∩
    {p | (q.val.2.2 : ℝ) ≤ p.2 - p.1}

/-- Each rational pair region is compact. -/
theorem isCompact_region (q : RationalScalarPairWindow) : IsCompact q.region :=
  (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const (continuous_snd.sub continuous_fst))

/-- The region lies in the strictly ordered part of its outer scalar square. -/
theorem region_subset (q : RationalScalarPairWindow) :
    q.region ⊆ {p | p.1 ∈ Icc (q.val.1 : ℝ) q.val.2.1 ∧
      p.2 ∈ Icc (q.val.1 : ℝ) q.val.2.1 ∧ p.1 < p.2} := by
  intro p hp
  have hgap : (0 : ℝ) < q.val.2.2 := by exact_mod_cast q.property.2
  exact ⟨hp.1.1, hp.1.2, sub_pos.mp (hgap.trans_le hp.2)⟩

/-- Pair loss in this region is bounded by the two original marginal scalar tails. -/
theorem measure_compl_region_le {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (q : RationalScalarPairWindow) (hπ : Vlasov.IsCoupling π μ ν)
    (hgap : ∀ᵐ p ∂π, (q.val.2.2 : ℝ) ≤ p.2 - p.1) :
    π q.regionᶜ ≤ (μ + ν) (Icc (q.val.1 : ℝ) q.val.2.1)ᶜ := by
  let I := Icc (q.val.1 : ℝ) (q.val.2.1 : ℝ)
  have hI : MeasurableSet I := measurableSet_Icc
  have hsub : ∀ᵐ p ∂π, p ∈ q.regionᶜ →
      p ∈ (Prod.fst ⁻¹' Iᶜ ∪ Prod.snd ⁻¹' Iᶜ : Set (ℝ × ℝ)) := by
    filter_upwards [hgap] with p hp
    intro hn
    by_cases hx : p.1 ∈ I
    · right
      intro hy
      exact hn ⟨⟨hx, hy⟩, hp⟩
    · exact Or.inl hx
  have hfst : π (Prod.fst ⁻¹' Iᶜ) = μ Iᶜ := by
    rw [← Measure.map_apply measurable_fst hI.compl, hπ.1]
  have hsnd : π (Prod.snd ⁻¹' Iᶜ) = ν Iᶜ := by
    rw [← Measure.map_apply measurable_snd hI.compl, hπ.2]
  calc
    π q.regionᶜ ≤ π (Prod.fst ⁻¹' Iᶜ ∪ Prod.snd ⁻¹' Iᶜ) := measure_mono_ae hsub
    _ ≤ π (Prod.fst ⁻¹' Iᶜ) + π (Prod.snd ⁻¹' Iᶜ) := measure_union_le _ _
    _ = (μ + ν) Iᶜ := by rw [hfst, hsnd, Measure.add_apply]

end RationalScalarPairWindow

/-- A finite scalar law carried by an open interval has rational inner compact
intervals losing arbitrarily little of that same law. -/
theorem exists_rational_inner_interval_mass
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hinside : ∀ᵐ t ∂μ, t ∈ Ioo a b) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ l r : ℚ, a < (l : ℝ) ∧ l < r ∧ (r : ℝ) < b ∧
      μ (Icc (l : ℝ) r)ᶜ < ε := by
  obtain ⟨K, _, hK, hsmall, _, hgood⟩ :=
    exists_lusin_compact_core_with_ae_property (s := univ) MeasurableSet.univ
      (measure_ne_top μ univ)
      (f := fun _ : ℝ ↦ (0 : ℝ)) measurable_const
      (P := fun t ↦ t ∈ Ioo a b) (by simpa only [Measure.restrict_univ] using hinside) hε
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by dsimp [c]; constructor <;> linarith
  let L := K ∪ {c}
  have hL : IsCompact L := hK.union isCompact_singleton
  have hLn : L.Nonempty := ⟨c, Or.inr rfl⟩
  have hLsub : L ⊆ Ioo a b := by
    intro x hx
    exact hx.elim (hgood x) (fun h ↦ (mem_singleton_iff.mp h).symm ▸ hc)
  have hlo := hLsub (hL.sInf_mem hLn)
  have hhi := hLsub (hL.sSup_mem hLn)
  obtain ⟨l, hal, hll⟩ := exists_rat_btwn hlo.1
  obtain ⟨r, hrr, hrb⟩ := exists_rat_btwn hhi.2
  have hbounds : L ⊆ Icc (l : ℝ) r := by
    intro x hx
    exact ⟨hll.le.trans (csInf_le hL.bddBelow hx),
      (le_csSup hL.bddAbove hx).trans hrr.le⟩
  have hlr : l < r := by
    have hminmax : sInf L ≤ sSup L :=
      (csInf_le hL.bddBelow (show c ∈ L from Or.inr rfl)).trans
        (le_csSup hL.bddAbove (show c ∈ L from Or.inr rfl))
    exact_mod_cast hll.trans_le hminmax |>.trans hrr
  refine ⟨l, r, hal, hlr, hrb, ?_⟩
  apply lt_of_le_of_lt (measure_mono ?_) hsmall
  intro x hx
  exact ⟨mem_univ _, fun hxK ↦ hx (hbounds (Or.inl hxK))⟩

/-- Rational pair windows with uniformly small coupling loss follow from the
original marginal support span and its actual positive physical separation. -/
theorem exists_rational_pair_window_of_support
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a b gap diam : ℝ} (hab : a < b) (hgap : 0 < gap)
    (ha : a ∈ (μ + ν).support) (hb : b ∈ (μ + ν).support)
    (hinside : ∀ᵐ t ∂μ + ν, t ∈ Ioo a b)
    (hsep : ConditionalClockSupportBounds μ ν gap diam)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ q : RationalScalarPairWindow,
      0 < (μ + ν) (Iio (q.val.1 : ℝ)) ∧
      0 < (μ + ν) (Ioi (q.val.2.1 : ℝ)) ∧
      (q.val.2.2 : ℝ) ≤ gap ∧ (μ + ν) (Icc (q.val.1 : ℝ) q.val.2.1)ᶜ < ε ∧
      ∀ π, Vlasov.IsCoupling π μ ν → (∀ᵐ p ∂π, p.1 ≤ p.2) → π q.regionᶜ < ε := by
  obtain ⟨l, r, hl, hlr, hr, hmass⟩ :=
    exists_rational_inner_interval_mass (μ + ν) hab hinside hε
  obtain ⟨d, hd0, hdgap⟩ := exists_rat_btwn hgap
  have hd : (0 : ℚ) < d := by exact_mod_cast hd0
  let q : RationalScalarPairWindow := ⟨(l, r, d), hlr, hd⟩
  have hleft := (Measure.mem_support_iff_forall _).mp ha _ (Iio_mem_nhds hl)
  have hright := (Measure.mem_support_iff_forall _).mp hb _ (Ioi_mem_nhds hr)
  refine ⟨q, hleft, hright, hdgap.le, hmass, ?_⟩
  intro π hπ horder
  apply (q.measure_compl_region_le hπ ?_).trans_lt hmass
  filter_upwards [hsep.ae_clock_gap_of_coupling hπ horder] with p hp
  exact hdgap.le.trans hp

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- Any strictly interior scalar endpoints have positive original mass outside both ends. -/
theorem OriginalSeedConditionalMoments.exterior_mass_pos
    {S : F.CalibratedLevelSeedPatch u} {w : S.covector.ker} {μ ν : Measure ℝ}
    (D : OriginalSeedConditionalMoments S w μ ν) {l r : ℝ}
    (hl : (S.level : ℝ) + D.lo < l) (hr : r < (S.level : ℝ) + D.hi) :
    0 < (μ + ν) (Iio l) ∧ 0 < (μ + ν) (Ioi r) := by
  have hleft : (S.level : ℝ) + D.lo ∈ (μ + ν).support := by
    rw [Measure.support_add]
    exact D.support.left_mem_support
  have hright : (S.level : ℝ) + D.hi ∈ (μ + ν).support := by
    rw [Measure.support_add]
    exact D.support.right_mem_support
  exact ⟨(Measure.mem_support_iff_forall _).mp hleft _ (Iio_mem_nhds hl),
    (Measure.mem_support_iff_forall _).mp hright _ (Ioi_mem_nhds hr)⟩

omit [BorelSpace E] in
/-- One rational compact pair window loses arbitrarily little mass uniformly over
all original legal couplings, with the gap supplied by the original physical supports. -/
theorem OriginalSeedConditionalMoments.exists_rational_pair_window
    {S : F.CalibratedLevelSeedPatch u} {w : S.covector.ker} {μ ν : Measure ℝ}
    (D : OriginalSeedConditionalMoments S w μ ν) {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : ConditionalClockSupportBounds μ ν gap diam)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ q : RationalScalarPairWindow,
      0 < (μ + ν) (Iio (q.val.1 : ℝ)) ∧
      0 < (μ + ν) (Ioi (q.val.2.1 : ℝ)) ∧
      (q.val.2.2 : ℝ) ≤ gap ∧ (μ + ν) (Icc (q.val.1 : ℝ) q.val.2.1)ᶜ < ε ∧
      ∀ π, Vlasov.IsCoupling π μ ν → (∀ᵐ p ∂π, p.1 ≤ p.2) → π q.regionᶜ < ε := by
  have := D.support.source.probability
  have := D.support.target.probability
  have hinside : ∀ᵐ t ∂μ + ν, t ∈ Ioo ((S.level : ℝ) + D.lo) ((S.level : ℝ) + D.hi) := by
    apply ae_add_measure_iff.mpr
    constructor
    · filter_upwards [D.support.source.ae_open] with t ht
      constructor <;> linarith only [ht.1, ht.2]
    · filter_upwards [D.support.target.ae_open] with t ht
      constructor <;> linarith only [ht.1, ht.2]
  have hl : (S.level : ℝ) + D.lo ∈ (μ + ν).support := by
    rw [Measure.support_add]
    exact D.support.left_mem_support
  have hr : (S.level : ℝ) + D.hi ∈ (μ + ν).support := by
    rw [Measure.support_add]
    exact D.support.right_mem_support
  have result := exists_rational_pair_window_of_support (μ := μ) (ν := ν)
    (a := (S.level : ℝ) + D.lo) (b := (S.level : ℝ) + D.hi)
    (gap := gap) (diam := diam) (ε := ε)
    (by linarith only [D.support.lt]) hgap hl hr hinside hsep hε
  exact result

end OTSelector.Reconstruction

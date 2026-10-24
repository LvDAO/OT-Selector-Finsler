import OTSelector.Reconstruction.OriginalFiniteOrderedMonochromeClassesGap

/-! Genuine finite ordered single-colour classes from separated scalar laws. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 600000

/-- A shared finite enumeration of the actual nonzero scalar classes. Adjacent
classes may have the same colour. Closed class covers retain support boundary
points, while the disjoint raw cells give the exact measure decomposition. -/
structure FiniteOrderedMonochromeClasses (μ ν : Measure ℝ) (δ : ℝ) where
  count : ℕ
  cell : Fin count → Set ℝ
  measurable_cell : ∀ i, MeasurableSet (cell i)
  compact_closure : ∀ i, IsCompact (closure (cell i))
  disjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j))
  nonzero : ∀ i, μ (cell i) + ν (cell i) ≠ 0
  monochrome : ∀ i, μ (cell i) = 0 ∨ ν (cell i) = 0
  source_sum : (∑ i, μ.restrict (cell i)) = μ
  target_sum : (∑ i, ν.restrict (cell i)) = ν
  opposite_gap : ∀ i j, i < j →
    ((μ (cell i) ≠ 0 ∧ ν (cell j) ≠ 0) ∨
      (ν (cell i) ≠ 0 ∧ μ (cell j) ≠ 0)) →
    ∀ x ∈ closure (cell i), ∀ y ∈ closure (cell j), δ / 2 ≤ y - x

/-- Removing zero combined-mass bins and sorting the retained actual thresholds
produces the shared finite classes. No forward coupling or Hall slack is an
input, and the restriction sums are the original laws exactly. -/
theorem exists_finiteOrderedMonochromeClasses_of_bins
    {I : Set ℝ} {δ D : ℝ} (Q : FiniteScalarBins I δ) (hI : IsCompact I)
    {μ ν : Measure ℝ} (hδ : 0 < δ) (hsep : ConditionalClockSupportBounds μ ν δ D)
    (hμI : ∀ᵐ x ∂μ, x ∈ I) (hνI : ∀ᵐ x ∂ν, x ∈ I) :
    Nonempty (FiniteOrderedMonochromeClasses μ ν δ) := by
  classical
  obtain ⟨e, he⟩ := exists_monotone_clockThreshold_permutation (fun i ↦ sInf (Q.cell i))
  let R : Finset (Fin Q.count) :=
    Finset.univ.filter (fun k ↦ μ (Q.cell (e k)) + ν (Q.cell (e k)) ≠ 0)
  let o : Fin R.card ≃o R := R.orderIsoOfFin rfl
  let pick : Fin R.card → Fin Q.count := fun i ↦ e (o i).val
  have hpick : Injective pick := by
    intro i j hij
    exact o.injective (Subtype.ext (e.injective hij))
  have hretained (i : Fin R.card) : μ (Q.cell (pick i)) + ν (Q.cell (pick i)) ≠ 0 :=
    (Finset.mem_filter.mp (o i).property).2
  have hlower : Monotone (fun i : Fin R.card ↦ sInf (Q.cell (pick i))) := by
    intro i j hij
    exact he (o.monotone hij)
  have hzero (k : Fin Q.count) (hk : k ∉ R) :
      μ (Q.cell (e k)) = 0 ∧ ν (Q.cell (e k)) = 0 := by
    have h : μ (Q.cell (e k)) + ν (Q.cell (e k)) = 0 := by
      by_contra hn
      exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    exact add_eq_zero.mp h
  have hsum (θ : Measure ℝ) (hθ : ∀ k, k ∉ R → θ (Q.cell (e k)) = 0)
      (hθI : ∀ᵐ x ∂θ, x ∈ I) :
      (∑ i : Fin R.card, θ.restrict (Q.cell (pick i))) = θ := by
    calc
      _ = ∑ k : R, θ.restrict (Q.cell (e k.val)) :=
        o.toEquiv.sum_comp (fun k : R ↦ θ.restrict (Q.cell (e k.val)))
      _ = ∑ k ∈ R, θ.restrict (Q.cell (e k)) :=
        (Finset.sum_subtype R (fun _ ↦ Iff.rfl)
          (fun k ↦ θ.restrict (Q.cell (e k)))).symm
      _ = ∑ k : Fin Q.count, θ.restrict (Q.cell (e k)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk
        exact Measure.restrict_eq_zero.mpr (hθ k hk)
      _ = ∑ k : Fin Q.count, θ.restrict (Q.cell k) :=
        e.sum_comp (fun k ↦ θ.restrict (Q.cell k))
      _ = θ.restrict I := by rw [← Measure.sum_fintype, Q.sum_restrict]
      _ = θ := Measure.restrict_eq_self_of_ae_mem hθI
  have hswap : ConditionalClockSupportBounds ν μ δ D :=
    { source_compact := hsep.target_compact
      target_compact := hsep.source_compact
      separated := fun s hs t ht ↦ by
        rw [dist_comm]
        exact hsep.separated t ht s hs
      diameter := fun s hs t ht ↦ hsep.diameter s
        (by simpa only [union_comm] using hs) t (by simpa only [union_comm] using ht) }
  refine ⟨⟨R.card, (fun i ↦ Q.cell (pick i)), (fun i ↦ Q.measurable_cell _),
    (fun i ↦ hI.of_isClosed_subset isClosed_closure (closure_minimal (Q.subset _) hI.isClosed)), ?_,
    hretained, (fun i ↦ Q.cell_mass_monochrome hδ hsep _),
    hsum μ (fun k hk ↦ (hzero k hk).1) hμI,
    hsum ν (fun k hk ↦ (hzero k hk).2) hνI, ?_⟩⟩
  · intro i j hij
    exact Q.disjoint (fun h ↦ hij (hpick h))
  · intro i j hij hcolours
    apply scalarRectangle_gap_closure
    rcases hcolours with h | h
    · exact Q.gap_of_positive_mass_lower_order hI hδ hsep h.1 h.2 (hlower hij.le)
    · exact Q.gap_of_positive_mass_lower_order hI hδ hswap h.1 h.2 (hlower hij.le)

/-- The actual compact, separated scalar support laws produce their own finite
ordered monochrome classes without caller-supplied bins or nonzero class data. -/
theorem exists_finiteOrderedMonochromeClasses
    {μ ν : Measure ℝ} {δ D : ℝ}
    (hδ : 0 < δ) (hsep : ConditionalClockSupportBounds μ ν δ D) :
    Nonempty (FiniteOrderedMonochromeClasses μ ν δ) := by
  obtain ⟨Q⟩ := exists_finiteScalarBins (hsep.source_compact.union hsep.target_compact) hδ
  apply exists_finiteOrderedMonochromeClasses_of_bins Q
    (hsep.source_compact.union hsep.target_compact) hδ hsep
  · have h : ∀ᵐ x ∂μ, x ∈ μ.support := μ.support_mem_ae
    exact h.mono fun _ hx ↦ Or.inl hx
  · have h : ∀ᵐ x ∂ν, x ∈ ν.support := ν.support_mem_ae
    exact h.mono fun _ hx ↦ Or.inr hx

/-- Exact class measures retain every original source point almost everywhere;
raw zero-mass cells are not asserted to retain all topological support points. -/
theorem FiniteOrderedMonochromeClasses.ae_source_cover
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) :
    ∀ᵐ x ∂μ, x ∈ ⋃ i, C.cell i := by
  have h : ∀ᵐ x ∂∑ i, μ.restrict (C.cell i), x ∈ ⋃ i, C.cell i := by
    apply ae_finsetSum_measure_iff.mpr
    intro i _
    exact (ae_restrict_mem (C.measurable_cell i)).mono fun x hx ↦ mem_iUnion.mpr ⟨i, hx⟩
  simpa only [C.source_sum] using h

/-- The target law has its own exact almost-everywhere raw-cell cover. -/
theorem FiniteOrderedMonochromeClasses.ae_target_cover
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) :
    ∀ᵐ x ∂ν, x ∈ ⋃ i, C.cell i := by
  have h : ∀ᵐ x ∂∑ i, ν.restrict (C.cell i), x ∈ ⋃ i, C.cell i := by
    apply ae_finsetSum_measure_iff.mpr
    intro i _
    exact (ae_restrict_mem (C.measurable_cell i)).mono fun x hx ↦ mem_iUnion.mpr ⟨i, hx⟩
  simpa only [C.target_sum] using h

/-- Closing the finite cells retains every topological support point of both
original laws, including boundary points in deleted zero-mass raw cells. -/
theorem FiniteOrderedMonochromeClasses.support_closed_cover
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) :
    μ.support ∪ ν.support ⊆ ⋃ i, closure (C.cell i) := by
  have hclosed : IsClosed (⋃ i, closure (C.cell i)) := isClosed_iUnion_of_finite fun _ ↦ isClosed_closure
  have hs : μ.support ⊆ ⋃ i, closure (C.cell i) :=
    Measure.support_subset_of_isClosed hclosed (C.ae_source_cover.mono fun _ hx ↦ by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, subset_closure hi⟩)
  have ht : ν.support ⊆ ⋃ i, closure (C.cell i) :=
    Measure.support_subset_of_isClosed hclosed (C.ae_target_cover.mono fun _ hx ↦ by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, subset_closure hi⟩)
  exact union_subset hs ht

/-- Each actual class has exactly one nonzero colour measure, with no
nonemptiness or positive-class assumption supplied by the caller. -/
theorem FiniteOrderedMonochromeClasses.restrict_monochrome
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) (i : Fin C.count) :
    μ.restrict (C.cell i) = 0 ∨ ν.restrict (C.cell i) = 0 :=
  (C.monochrome i).imp Measure.restrict_eq_zero.mpr Measure.restrict_eq_zero.mpr

/-- Every source/target class rectangle is completely legal or completely
backward according to the actual shared class order, including support closure. -/
theorem FiniteOrderedMonochromeClasses.source_target_legal_iff
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) (hδ : 0 < δ)
    {i j : Fin C.count} (hi : μ (C.cell i) ≠ 0) (hj : ν (C.cell j) ≠ 0)
    {x y : ℝ} (hx : x ∈ closure (C.cell i)) (hy : y ∈ closure (C.cell j)) :
    x < y ↔ i < j := by
  have hne : i ≠ j := by
    intro hij
    subst j
    exact (C.monochrome i).elim hi hj
  constructor
  · intro hxy
    by_contra hij
    have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm hne)
    have hgap := C.opposite_gap j i hji (Or.inr ⟨hj, hi⟩) y hy x hx
    linarith
  · intro hij
    have hgap := C.opposite_gap i j hij (Or.inl ⟨hi, hj⟩) x hx y hy
    linarith

/-- The same whole-rectangle gap holds for the genuine restricted laws'
supports, which may include endpoints absent from their raw measurable cells. -/
theorem FiniteOrderedMonochromeClasses.restricted_support_gap
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ)
    {i j : Fin C.count} (hij : i < j)
    {x y : ℝ} (hx : x ∈ (μ.restrict (C.cell i)).support)
    (hy : y ∈ (ν.restrict (C.cell j)).support) : δ / 2 ≤ y - x := by
  have hi : μ (C.cell i) ≠ 0 :=
    mt Measure.restrict_eq_zero.mpr (Measure.nonempty_support_iff.mp ⟨x, hx⟩)
  have hj : ν (C.cell j) ≠ 0 :=
    mt Measure.restrict_eq_zero.mpr (Measure.nonempty_support_iff.mp ⟨y, hy⟩)
  exact C.opposite_gap i j hij (Or.inl ⟨hi, hj⟩) x (Measure.support_restrict_subset hx).1
    y (Measure.support_restrict_subset hy).1

/-- Actual source and target restriction-support points determine the exact
class order without any caller-supplied class-mass positivity hypothesis. -/
theorem FiniteOrderedMonochromeClasses.restricted_support_legal_iff
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) (hδ : 0 < δ)
    {i j : Fin C.count} {x y : ℝ} (hx : x ∈ (μ.restrict (C.cell i)).support)
    (hy : y ∈ (ν.restrict (C.cell j)).support) : x < y ↔ i < j := by
  have hi : μ (C.cell i) ≠ 0 :=
    mt Measure.restrict_eq_zero.mpr (Measure.nonempty_support_iff.mp ⟨x, hx⟩)
  have hj : ν (C.cell j) ≠ 0 :=
    mt Measure.restrict_eq_zero.mpr (Measure.nonempty_support_iff.mp ⟨y, hy⟩)
  exact C.source_target_legal_iff hδ hi hj (Measure.support_restrict_subset hx).1
    (Measure.support_restrict_subset hy).1

/-- Every retained class has strictly positive actual combined mass. -/
theorem FiniteOrderedMonochromeClasses.class_mass_pos
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) (i : Fin C.count) :
    0 < μ (C.cell i) + ν (C.cell i) := pos_iff_ne_zero.mpr (C.nonzero i)

/-- Evaluating the exact measure decompositions gives the unchanged original
source and target class-mass sums, including empty zero-law enumerations. -/
theorem FiniteOrderedMonochromeClasses.mass_sums
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) :
    (∑ i, μ (C.cell i)) = μ univ ∧ (∑ i, ν (C.cell i)) = ν univ := by
  constructor
  · have h := congrArg (fun θ : Measure ℝ ↦ θ univ) C.source_sum
    simpa only [Measure.finsetSum_apply, Measure.restrict_apply_univ] using h
  · have h := congrArg (fun θ : Measure ℝ ↦ θ univ) C.target_sum
    simpa only [Measure.finsetSum_apply, Measure.restrict_apply_univ] using h

/-- For the original finite laws, every retained class has positive real mass;
there is no conversion of infinite mass to zero in this readout. -/
theorem FiniteOrderedMonochromeClasses.real_class_mass_pos
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {δ : ℝ}
    (C : FiniteOrderedMonochromeClasses μ ν δ) (i : Fin C.count) :
    0 < μ.real (C.cell i) + ν.real (C.cell i) := by
  have hm : μ (C.cell i) + ν (C.cell i) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top ν _⟩
  have h := ENNReal.toReal_pos (C.nonzero i) hm
  simpa only [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top ν _), measureReal_def] using h

end OTSelector.Reconstruction

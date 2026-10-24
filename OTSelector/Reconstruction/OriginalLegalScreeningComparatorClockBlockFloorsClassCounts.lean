import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockFloorsCounts

/-! Adjacent real grid-prefix readouts control the actual protected extreme classes. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- Counts on disjoint real mark classes add on the same original sampler indices. -/
theorem originalReserveBlockCount_union {n : ℕ} {marks : ℕ → ℝ} {U V : Set ℝ}
    (hUV : Disjoint U V) : originalReserveBlockCount n marks (U ∪ V) =
      originalReserveBlockCount n marks U + originalReserveBlockCount n marks V := by
  classical
  unfold originalReserveBlockCount originalReserveClassNatIndices
  have he : (Finset.range n).filter (fun i ↦ marks i ∈ U ∪ V) =
      (Finset.range n).filter (fun i ↦ marks i ∈ U) ∪ (Finset.range n).filter (fun i ↦ marks i ∈ V) := by
    ext i
    simp only [Finset.mem_filter,mem_union,Finset.mem_union]
    tauto
  have hd : Disjoint ((Finset.range n).filter (fun i ↦ marks i ∈ U))
      ((Finset.range n).filter (fun i ↦ marks i ∈ V)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Set.disjoint_left.mp hUV (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  convert (congrArg Finset.card he).trans (Finset.card_union_of_disjoint hd) using 1
  congr 1
  ext i
  simp only [Finset.mem_filter]

/-- Consecutive original grid prefixes telescope to the literal source Ico/target Ioc class count. -/
theorem originalReserveBlockCount_grid_increment (n : ℕ) (marks : ℕ → ℝ)
    {a s t : ℝ} (has : a ≤ s) (hst : s ≤ t) :
    originalReserveBlockCount n marks (Ico a t) =
      originalReserveBlockCount n marks (Ico a s) + originalReserveBlockCount n marks (Ico s t) ∧
    originalReserveBlockCount n marks (Ioc a t) =
      originalReserveBlockCount n marks (Ioc a s) + originalReserveBlockCount n marks (Ioc s t) := by
  constructor
  · rw [← Ico_union_Ico_eq_Ico has hst]
    apply originalReserveBlockCount_union
    exact Set.disjoint_left.mpr (fun _ hx hy ↦ not_lt_of_ge hy.1 hx.2)
  · rw [← Ioc_union_Ioc_eq_Ioc has hst]
    apply originalReserveBlockCount_union
    exact Set.disjoint_left.mpr (fun _ hx hy ↦ not_lt_of_ge hx.2 hy.1)

/-- Actual law masses have the same exact adjacent-prefix increment, with atoms retained. -/
theorem originalClockLaw_grid_increment (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a s t : ℝ} (has : a ≤ s) (hst : s ≤ t) :
    μ.real (Ico a t) = μ.real (Ico a s) + μ.real (Ico s t) ∧
    μ.real (Ioc a t) = μ.real (Ioc a s) + μ.real (Ioc s t) := by
  constructor
  · rw [← Ico_union_Ico_eq_Ico has hst]
    exact measureReal_union (Set.disjoint_left.mpr (fun _ hx hy ↦ not_lt_of_ge hy.1 hx.2)) measurableSet_Ico
  · rw [← Ioc_union_Ioc_eq_Ioc has hst]
    exact measureReal_union (Set.disjoint_left.mpr (fun _ hx hy ↦ not_lt_of_ge hx.2 hy.1)) measurableSet_Ioc

/-- Two neighboring true raw-prefix errors cost at most twice that error in
one original mark class. This conclusion is a count estimate, without a class positivity input. -/
theorem originalReserveBlockCount_grid_increment_lower
    (n : ℕ) (marks : ℕ → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a s t θ V e : ℝ} (has : a ≤ s) (hst : s ≤ t)
    (hs : |(originalReserveBlockCount n marks (Ico a s) : ℝ)-θ*V*μ.real (Ico a s)| ≤ e*V)
    (ht : |(originalReserveBlockCount n marks (Ico a t) : ℝ)-θ*V*μ.real (Ico a t)| ≤ e*V) :
    θ*V*μ.real (Ico s t)-2*e*V ≤ (originalReserveBlockCount n marks (Ico s t) : ℝ) := by
  have hc := (originalReserveBlockCount_grid_increment n marks has hst).1
  have hm := (originalClockLaw_grid_increment μ has hst).1
  have hcr : (originalReserveBlockCount n marks (Ico a t) : ℝ) =
      (originalReserveBlockCount n marks (Ico a s) : ℝ)+(originalReserveBlockCount n marks (Ico s t) : ℝ) := by
    exact_mod_cast hc
  rw [hm] at ht
  have hl := (abs_le.mp ht).1
  have hu := (abs_le.mp hs).2
  nlinarith only [hcr,hl,hu]

/-- The target endpoint uses Ioc throughout the same adjacent-prefix calculation. -/
theorem originalReserveBlockCount_target_grid_increment_lower
    (n : ℕ) (marks : ℕ → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a s t θ V e : ℝ} (has : a ≤ s) (hst : s ≤ t)
    (hs : |(originalReserveBlockCount n marks (Ioc a s) : ℝ)-θ*V*μ.real (Ioc a s)| ≤ e*V)
    (ht : |(originalReserveBlockCount n marks (Ioc a t) : ℝ)-θ*V*μ.real (Ioc a t)| ≤ e*V) :
    θ*V*μ.real (Ioc s t)-2*e*V ≤ (originalReserveBlockCount n marks (Ioc s t) : ℝ) := by
  have hc := (originalReserveBlockCount_grid_increment n marks has hst).2
  have hm := (originalClockLaw_grid_increment μ has hst).2
  have hcr : (originalReserveBlockCount n marks (Ioc a t) : ℝ) =
      (originalReserveBlockCount n marks (Ioc a s) : ℝ)+(originalReserveBlockCount n marks (Ioc s t) : ℝ) := by
    exact_mod_cast hc
  rw [hm] at ht
  have hl := (abs_le.mp ht).1
  have hu := (abs_le.mp hs).2
  nlinarith only [hcr,hl,hu]

end OTSelector.Reconstruction

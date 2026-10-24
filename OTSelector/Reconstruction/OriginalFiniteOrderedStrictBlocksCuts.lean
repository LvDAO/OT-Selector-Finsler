import OTSelector.Reconstruction.OriginalFiniteOrderedMonochromeClasses

/-! Actual consecutive zero-prefix cuts form a finite strict block partition. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 500000

/-- A pair of zero cuts is consecutive when every proper intervening prefix
has nonzero surplus. This definition constructs blocks from all tight cuts. -/
def IsConsecutiveSurplusZeroCut (H : ℕ → ℝ) {N : ℕ}
    (l r : Fin (N + 1)) : Prop :=
  l < r ∧ H l.val = 0 ∧ H r.val = 0 ∧
    ∀ k : Fin (N + 1), l < k → k < r → H k.val ≠ 0

/-- All consecutive zero-cut pairs form an actual finite set. -/
def finiteSurplusZeroCutPairs (H : ℕ → ℝ) (N : ℕ) :
    Finset (Fin (N + 1) × Fin (N + 1)) := by
  classical
  exact Finset.univ.filter (fun p ↦ IsConsecutiveSurplusZeroCut H p.1 p.2)

/-- The finite block index consists of the consecutive zero-cut pairs themselves. -/
abbrev FiniteSurplusStrictBlock (H : ℕ → ℝ) (N : ℕ) :=
  ↥(finiteSurplusZeroCutPairs H N)

/-- The lower actual tight cut of a finite block. -/
def FiniteSurplusStrictBlock.lower {H : ℕ → ℝ} {N : ℕ}
    (b : FiniteSurplusStrictBlock H N) : Fin (N + 1) := b.val.1

/-- The upper actual tight cut of a finite block. -/
def FiniteSurplusStrictBlock.upper {H : ℕ → ℝ} {N : ℕ}
    (b : FiniteSurplusStrictBlock H N) : Fin (N + 1) := b.val.2

/-- Each indexed block retains its true consecutive-zero-cut certificate. -/
theorem FiniteSurplusStrictBlock.consecutive {H : ℕ → ℝ} {N : ℕ}
    (b : FiniteSurplusStrictBlock H N) : IsConsecutiveSurplusZeroCut H b.lower b.upper := by
  classical
  exact (Finset.mem_filter.mp b.property).2

/-- A class belongs to the half-open interval between a block's actual tight cuts. -/
def FiniteSurplusStrictBlock.Contains {H : ℕ → ℝ} {N : ℕ}
    (b : FiniteSurplusStrictBlock H N) (i : Fin N) : Prop :=
  b.lower.val ≤ i.val ∧ i.val < b.upper.val

/-- Every original class lies in a unique consecutive-zero-cut block. Endpoint
zero cuts suffice; no strict interior surplus assumption is used. -/
theorem exists_unique_finiteSurplusStrictBlock
    (H : ℕ → ℝ) (N : ℕ) (h₀ : H 0 = 0) (hN : H N = 0) (i : Fin N) :
    ∃! b : FiniteSurplusStrictBlock H N, b.Contains i := by
  classical
  let L : Finset (Fin (N + 1)) :=
    Finset.univ.filter (fun k ↦ k.val ≤ i.val ∧ H k.val = 0)
  let R : Finset (Fin (N + 1)) :=
    Finset.univ.filter (fun k ↦ i.val < k.val ∧ H k.val = 0)
  have hL : L.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using h₀⟩⟩
  have hR : R.Nonempty := ⟨Fin.last N, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, by simpa using And.intro i.isLt hN⟩⟩
  let l := L.max' hL
  let r := R.min' hR
  have hl : l.val ≤ i.val ∧ H l.val = 0 := (Finset.mem_filter.mp (L.max'_mem hL)).2
  have hr : i.val < r.val ∧ H r.val = 0 := (Finset.mem_filter.mp (R.min'_mem hR)).2
  have hlr : l < r := by exact hl.1.trans_lt hr.1
  have hinner : ∀ k : Fin (N + 1), l < k → k < r → H k.val ≠ 0 := by
    intro k hlk hkr hk
    by_cases hki : k.val ≤ i.val
    · have hkL : k ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hki, hk⟩
      exact not_lt_of_ge (L.le_max' k hkL) hlk
    · have hkR : k ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hki, hk⟩
      exact not_lt_of_ge (R.min'_le k hkR) hkr
  let b : FiniteSurplusStrictBlock H N :=
    ⟨(l, r), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlr, hl.2, hr.2, hinner⟩⟩
  refine ⟨b, ⟨hl.1, hr.1⟩, ?_⟩
  intro c hc
  have hcl : c.lower = l := by
    have hcle : c.lower ≤ l := L.le_max' c.lower
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.1, c.consecutive.2.1⟩)
    apply le_antisymm hcle
    by_contra h
    have hlc : c.lower < l := lt_of_not_ge h
    exact c.consecutive.2.2.2 l hlc (by exact hl.1.trans_lt hc.2) hl.2
  have hcr : c.upper = r := by
    have hrle : r ≤ c.upper := R.min'_le c.upper
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.2, c.consecutive.2.2.1⟩)
    apply le_antisymm ?_ hrle
    by_contra h
    have hrc : r < c.upper := lt_of_not_ge h
    exact c.consecutive.2.2.2 r (by rw [hcl]; exact hlr) hrc hr.2
  apply Subtype.ext
  exact Prod.ext hcl hcr

/-- Weak nonnegativity and the construction from every zero cut make all
proper block prefixes strictly positive. -/
theorem FiniteSurplusStrictBlock.proper_prefix_pos
    {H : ℕ → ℝ} {N : ℕ} (b : FiniteSurplusStrictBlock H N)
    (hH : ∀ k ≤ N, 0 ≤ H k) {k : Fin (N + 1)}
    (hlk : b.lower < k) (hkr : k < b.upper) : 0 < H k.val :=
  lt_of_le_of_ne (hH k.val (Nat.le_of_lt_succ k.isLt))
    (Ne.symm (b.consecutive.2.2.2 k hlk hkr))

/-- A finite positive lower bound for every actual proper block prefix is
constructed internally; a one-step empty prefix family is harmless. -/
theorem FiniteSurplusStrictBlock.exists_uniform_proper_prefix_pos
    {H : ℕ → ℝ} {N : ℕ} (b : FiniteSurplusStrictBlock H N)
    (hH : ∀ k ≤ N, 0 ≤ H k) :
    ∃ η : ℝ, 0 < η ∧ ∀ k : Fin (N + 1), b.lower < k → k < b.upper → η ≤ H k.val := by
  classical
  let K : Finset (Fin (N + 1)) := Finset.univ.filter (fun k ↦ b.lower < k ∧ k < b.upper)
  by_cases hK : K.Nonempty
  · refine ⟨K.inf' hK (fun k ↦ H k.val), ?_, ?_⟩
    · apply (Finset.lt_inf'_iff hK).mpr
      intro k hk
      exact b.proper_prefix_pos hH (Finset.mem_filter.mp hk).2.1 (Finset.mem_filter.mp hk).2.2
    · intro k hlk hkr
      exact Finset.inf'_le (s := K) (fun k : Fin (N + 1) ↦ H k.val) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlk, hkr⟩)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro k hlk hkr
    exact False.elim (hK ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlk, hkr⟩⟩)

end OTSelector.Reconstruction

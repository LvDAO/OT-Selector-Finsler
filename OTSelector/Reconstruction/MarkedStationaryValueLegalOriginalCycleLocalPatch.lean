import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCountingPairSelection
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalTwoEdgeSwapMeasurable

/-!
# A measurable legal improving patch on the same original full matching

A Borel certificate selects actual occupied original edges through their shell
code. The resulting measurable patch preserves the complete original input,
all integer matching constraints and strict forward legality. This is the local
operation used once per disjoint coarse cell in the stationary competitor.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false

/-- A Borel legal pair certificate produces an actual measurable same-input
patch, applied exactly when a certified original support pair exists. -/
theorem exists_measurable_originalLegalPairSwap
    {q : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (s : Ω → LegalMarkedOptimalInputScene q) (hs : Measurable s)
    (R : Ω → LegalMarkedPhysicalEdge q × LegalMarkedPhysicalEdge q → Prop)
    (hR : MeasurableSet {p : Ω × (LegalMarkedPhysicalEdge q × LegalMarkedPhysicalEdge q) |
      R p.1 p.2})
    (hlegal : ∀ ω e f, R ω (e, f) →
      e ≠ f ∧ e.1.2 < f.2.2 ∧ f.1.2 < e.2.2) :
    ∃ Φ : Ω → LegalMarkedOptimalInputScene q,
      Measurable Φ ∧ (∀ ω, (Φ ω).2 = (s ω).2) ∧
      ∀ ω, IsFullOriginalInputMatching q (s ω) →
        (∀ e ∈ ((s ω).1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2) →
        IsFullOriginalInputMatching q (Φ ω) ∧
        (∀ e ∈ ((Φ ω).1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2) ∧
        ((∃ e ∈ ((s ω).1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
          ∃ f ∈ ((s ω).1.1 : Measure (LegalMarkedPhysicalEdge q)).support, R ω (e, f)) →
          ∃ e ∈ ((s ω).1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
            ∃ f ∈ ((s ω).1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
              R ω (e, f) ∧ Φ ω = originalTwoEdgeSwapScene (s ω) e f) ∧
        ((¬ ∃ e ∈ ((s ω).1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
          ∃ f ∈ ((s ω).1.1 : Measure (LegalMarkedPhysicalEdge q)).support, R ω (e, f)) →
          Φ ω = s ω) := by
  let base : LegalMarkedPhysicalEdge q := 0
  let μ : Ω → LocalFiniteMeasure (LegalMarkedPhysicalEdge q) := fun ω ↦ (s ω).1.1
  have hμ : Measurable μ := hs.fst.fst
  obtain ⟨choose, hchoose, hspec⟩ := exists_measurable_originalCountingPair_selection
    base μ hμ R hR
  let Bad : Set Ω := {ω | ∃ n, originalCountingPairWitness base (μ ω) (R ω) n}
  have hBad : MeasurableSet Bad :=
    measurableSet_exists_originalCountingPairWitness base μ hμ R hR
  let Φ : Ω → LegalMarkedOptimalInputScene q := fun ω ↦
    if ω ∈ Bad then originalTwoEdgeSwapScene (s ω) (choose ω).1 (choose ω).2 else s ω
  refine ⟨Φ, ?_, ?_, ?_⟩
  · change Measurable (fun ω ↦ if ω ∈ Bad then
      originalTwoEdgeSwapScene (s ω) (choose ω).1 (choose ω).2 else s ω)
    apply Measurable.ite hBad
    · change Measurable ((fun p : LegalMarkedOptimalInputScene q ×
        (LegalMarkedPhysicalEdge q × LegalMarkedPhysicalEdge q) ↦
        originalTwoEdgeSwapScene p.1 p.2.1 p.2.2) ∘ (fun ω ↦ (s ω, choose ω)))
      have hi : Measurable (fun ω ↦ (s ω, choose ω)) := hs.prodMk hchoose
      exact (measurable_originalTwoEdgeSwapScene q).comp hi
    · exact hs
  · intro ω
    dsimp only [Φ]
    split_ifs <;> rfl
  · intro ω hfull hforward
    have hcount : IsLegalCountingMeasure base (μ ω) :=
      ((isLegalSimpleCountingMeasure_iff _ _).mp hfull.simple_edges).1
    have hiff : ω ∈ Bad ↔
        ∃ e ∈ ((s ω).1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
          ∃ f ∈ ((s ω).1.1 : Measure (LegalMarkedPhysicalEdge q)).support, R ω (e, f) :=
      exists_originalCountingPairWitness_iff base (μ ω) hcount (R ω)
    by_cases hb : ω ∈ Bad
    · have hselected := hspec ω hcount (hiff.mp hb)
      have hleg := hlegal ω (choose ω).1 (choose ω).2 hselected.2.2
      have hΦ : Φ ω = originalTwoEdgeSwapScene (s ω) (choose ω).1 (choose ω).2 :=
        ite_eq_left hb
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hΦ]
        exact hfull.twoEdgeSwap hselected.1 hselected.2.1 hleg.1
      · rw [hΦ]
        exact forward_originalTwoEdgeSwapScene (s ω) hforward _ _ hleg.2.1 hleg.2.2
      · intro _
        exact ⟨(choose ω).1, hselected.1, (choose ω).2, hselected.2.1, hselected.2.2, hΦ⟩
      · intro hnone
        exact (hnone (hiff.mp hb)).elim
    · have hΦ : Φ ω = s ω := ite_eq_right hb
      refine ⟨hΦ.symm ▸ hfull, hΦ.symm ▸ hforward, ?_, fun _ ↦ hΦ⟩
      intro hgood
      exact (hb (hiff.mpr hgood)).elim

/-- A bounded complete-edge window and a fixed positive saving give a Borel
local certificate for the unchanged original edge cost. -/
def originalLegalCycleCertificate {q : ℕ}
    (c : LegalMarkedPhysicalEdge q → ℝ) (K : Set (LegalMarkedPhysicalEdge q))
    (ε : ℝ) (p : LegalMarkedPhysicalEdge q × LegalMarkedPhysicalEdge q) : Prop :=
  p.1 ≠ p.2 ∧ p.1 ∈ K ∧ p.2 ∈ K ∧
    p.1.1.2 < p.2.2.2 ∧ p.2.1.2 < p.1.2.2 ∧
      ε ≤ c p.1 + c p.2 - c (p.1.1, p.2.2) - c (p.2.1, p.1.2)

/-- The strict legal improvement event uses only original Borel edge data. -/
theorem measurableSet_originalLegalCycleCertificate {q : ℕ}
    (c : LegalMarkedPhysicalEdge q → ℝ) (hc : Measurable c)
    {K : Set (LegalMarkedPhysicalEdge q)} (hK : MeasurableSet K) (ε : ℝ) :
    MeasurableSet {p | originalLegalCycleCertificate c K ε p} := by
  apply (measurableSet_eq_fun measurable_fst measurable_snd).compl.inter
  apply (measurable_fst hK).inter
  apply (measurable_snd hK).inter
  apply (measurableSet_lt measurable_fst.fst.snd measurable_snd.snd.snd).inter
  apply (measurableSet_lt measurable_snd.fst.snd measurable_fst.snd.snd).inter
  exact measurableSet_le measurable_const
    ((((hc.comp measurable_fst).add (hc.comp measurable_snd)).sub
      (hc.comp (measurable_fst.fst.prodMk measurable_snd.snd))).sub
        (hc.comp (measurable_snd.fst.prodMk measurable_fst.snd)))

/-- The certificate forces precisely the two original legal crossed clocks. -/
theorem originalLegalCycleCertificate_legal {q : ℕ}
    (c : LegalMarkedPhysicalEdge q → ℝ) (K : Set (LegalMarkedPhysicalEdge q)) (ε : ℝ)
    (e f : LegalMarkedPhysicalEdge q) (h : originalLegalCycleCertificate c K ε (e, f)) :
    e ≠ f ∧ e.1.2 < f.2.2 ∧ f.1.2 < e.2.2 :=
  ⟨h.1, h.2.2.2.1, h.2.2.2.2.1⟩

end OTSelector.Reconstruction

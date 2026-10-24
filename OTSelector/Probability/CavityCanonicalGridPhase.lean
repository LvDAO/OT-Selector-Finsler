import OTSelector.Probability.CavitySemidiscreteGridPhase

/-! Canonical actual Ioc grid phases and exact original lattice reindexing. -/
open Set Function MeasureTheory
noncomputable section
namespace OTSelector.Probability
variable (ι : Type*) (ell : ℝ) [Fact (0 < ell)]

/-- The actual coordinatewise representative in the existing phase cell (0,ell]. -/
def cavityGridCanonicalPhase (x : ι → ℝ) : ι → ℝ := fun i ↦
  (AddCircle.equivIoc ell 0 (x i : AddCircle ell) : ℝ)

theorem measurable_cavityGridCanonicalPhase : Measurable (cavityGridCanonicalPhase ι ell) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_subtype_coe.comp ((AddCircle.measurableEquivIoc ell 0).measurable.comp
    (AddCircle.measurable_mk'.comp (measurable_pi_apply i)))

theorem cavityGridCanonicalPhase_mem (x : ι → ℝ) :
    cavityGridCanonicalPhase ι ell x ∈ cavityGridPhaseCell ι ell := by
  intro i _
  simpa only [zero_add, cavityGridCanonicalPhase] using (AddCircle.equivIoc ell 0 (x i : AddCircle ell)).property

theorem cavityGridCanonicalPhase_of_mem {x : ι → ℝ} (hx : x ∈ cavityGridPhaseCell ι ell) :
    cavityGridCanonicalPhase ι ell x = x := by
  funext i
  exact AddCircle.equivIoc_coe_of_mem (by simpa only [zero_add] using hx i (mem_univ i))

theorem cavityGridCanonicalPhase_vadd (g : CavityGridLattice ι ell) (x : ι → ℝ) :
    cavityGridCanonicalPhase ι ell (g +ᵥ x) = cavityGridCanonicalPhase ι ell x := by
  funext i
  have hg : ((g i : ℝ) : AddCircle ell) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr (g i).property
  change (AddCircle.equivIoc ell 0 (((g i : ℝ) + x i : ℝ) : AddCircle ell) : ℝ) = _
  simp only [AddCircle.coe_add, hg, zero_add, cavityGridCanonicalPhase]

/-- The exact original lattice displacement removed by canonicalization. -/
def cavityGridCanonicalOffset (x : ι → ℝ) : CavityGridLattice ι ell := fun i ↦
  ⟨x i - cavityGridCanonicalPhase ι ell x i, by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change ((x i - (AddCircle.equivIoc ell 0 (x i : AddCircle ell) : ℝ) : ℝ) : AddCircle ell) = 0
    rw [AddCircle.coe_sub, AddCircle.coe_equivIoc, sub_self]⟩

theorem cavityGridCanonicalOffset_vadd_phase (x : ι → ℝ) :
    cavityGridCanonicalOffset ι ell x +ᵥ cavityGridCanonicalPhase ι ell x = x := by
  funext i
  change x i - cavityGridCanonicalPhase ι ell x i + cavityGridCanonicalPhase ι ell x i = x i
  exact sub_add_cancel _ _

/-- Physical rerooting x↦x−v canonically changes the existing grid phase. -/
def cavityGridPhaseReroot (v u : ι → ℝ) : ι → ℝ :=
  cavityGridCanonicalPhase ι ell (u - v)

/-- The original grid base after rerooting is exactly a reindexed base with
its new canonical phase. -/
theorem cavityGrid_reindex_base (g : CavityGridLattice ι ell) (u v : ι → ℝ) :
    (g + cavityGridCanonicalOffset ι ell (u - v)) +ᵥ cavityGridPhaseReroot ι ell v u =
      (g +ᵥ u) - v := by
  funext i
  change (g i : ℝ) + (u i - v i - cavityGridCanonicalPhase ι ell (u - v) i) +
      cavityGridCanonicalPhase ι ell (u - v) i = (g i : ℝ) + u i - v i
  ring

end OTSelector.Probability

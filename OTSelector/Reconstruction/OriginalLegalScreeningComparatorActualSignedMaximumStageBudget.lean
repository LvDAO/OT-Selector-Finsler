import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairActualClockBlock
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedMean

/-! Genuine clock-block stage budgets reindex to the original finite stage family. -/
open Set Function MeasureTheory Module Manifold TopologicalSpace
open scoped BigOperators ENNReal Classical ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
namespace OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- Every local stage is exactly one original fine class, including the empty grid. -/
def originalBlockStageEquiv (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) :
    (Σ block : G.ClockSlabBlock μ ν, Fin (block.upper.val-block.lower.val)) ≃ Fin G.count :=
  Equiv.ofBijective (fun p ↦ ⟨p.1.lower.val+p.2.val,by have h := p.1.upper.isLt; have hh := p.2.isLt; omega⟩) (by
    constructor
    · rintro ⟨b,k⟩ ⟨c,l⟩ he
      have hki : b.Contains (⟨b.lower.val+k.val,by have h := b.upper.isLt; have hh := k.isLt; omega⟩ : Fin G.count) := by
        change b.lower.val ≤ b.lower.val+k.val ∧ b.lower.val+k.val < b.upper.val
        have hh := k.isLt
        omega
      have hli : c.Contains (⟨c.lower.val+l.val,by have h := c.upper.isLt; have hh := l.isLt; omega⟩ : Fin G.count) := by
        change c.lower.val ≤ c.lower.val+l.val ∧ c.lower.val+l.val < c.upper.val
        have hh := l.isLt
        omega
      change (⟨b.lower.val+k.val,_⟩ : Fin G.count) = ⟨c.lower.val+l.val,_⟩ at he
      have hbc : b = c := (exists_unique_finiteSurplusStrictBlock _ _ h₀ hN _).unique hki (he.symm ▸ hli)
      subst c
      have hkl : k = l := Fin.ext (by have hh := congrArg Fin.val he; dsimp only at hh; omega)
      subst l
      rfl
    · intro i
      have hi := G.blockForClass_contains h₀ hN i
      refine ⟨⟨G.blockForClass h₀ hN i,⟨i.val-(G.blockForClass h₀ hN i).lower.val,?_⟩⟩,?_⟩
      · dsimp only [FiniteSurplusStrictBlock.Contains] at hi
        omega
      · apply Fin.ext
        dsimp only [FiniteSurplusStrictBlock.Contains] at hi
        dsimp only
        omega)

/-- Local stage sums have exactly the original fine-class weights. -/
theorem sum_originalBlock_stages (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0) (a : G.ClockSlabBlock μ ν → ℝ) (f : Fin G.count → ℝ) :
    (∑ block : G.ClockSlabBlock μ ν, a block *
      ∑ k : Fin (block.upper.val-block.lower.val),
        f ⟨block.lower.val+k.val,by have h := block.upper.isLt; have hh := k.isLt; omega⟩) =
      ∑ i, a (G.blockForClass h₀ hN i)*f i := by
  simp_rw [Finset.mul_sum]

  have hb (p : Σ block : G.ClockSlabBlock μ ν, Fin (block.upper.val-block.lower.val)) :
      G.blockForClass h₀ hN (G.originalBlockStageEquiv h₀ hN p) = p.1 := by
    apply (G.blockForClass_eq_iff h₀ hN _ _).mpr
    change p.1.lower.val ≤ p.1.lower.val+p.2.val ∧ p.1.lower.val+p.2.val < p.1.upper.val
    have hh := p.2.isLt
    omega
  calc
    _ = ∑ p : Σ block : G.ClockSlabBlock μ ν, Fin (block.upper.val-block.lower.val),
        a p.1 * f (G.originalBlockStageEquiv h₀ hN p) := by
      rw [Fintype.sum_sigma]
      rfl
    _ = _ := by
      simpa only [hb] using (G.originalBlockStageEquiv h₀ hN).sum_comp
        (fun i ↦ a (G.blockForClass h₀ hN i)*f i)

end OriginalStageClockGrid

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The real Neumann coefficient paid by the stages inside one actual clock block. -/
def originalClockBlockStageRepairBudget
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) (R ell ρ : ℝ)
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _))
    (block : G.ClockSlabBlock μ ν) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  3*((block.upper.val-block.lower.val : ℕ) : ℝ)*
    ∑ k : Fin (block.upper.val-block.lower.val),
      let i : Fin G.count := ⟨block.lower.val+k.val,by have h := block.upper.isLt; have hh := k.isLt; omega⟩
      ρ⁻¹*originalOrientedStageCurrentInputNeumannBudget S w Q b (K i) R ell
        (G.cut i.val) (G.cut (i.val+1)) (hj i) scene

omit [BorelSpace E] in
/-- Actual block stage costs are nonnegative, also on zero-law blocks. -/
theorem originalClockBlockStageRepairBudget_nonneg
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) {R : ℝ} (hR : 0 ≤ R) (ell : ℝ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2 (Q.law : Measure _))
    (block : G.ClockSlabBlock μ ν) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    0 ≤ originalClockBlockStageRepairBudget Q G b K R ell ρ hj block scene := by
  apply mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (inv_nonneg.mpr hρ)
    (originalOrientedStageCurrentInputNeumannBudget_nonneg Q b _ hR ell _ _ _ scene)

end OTSelector.Reconstruction

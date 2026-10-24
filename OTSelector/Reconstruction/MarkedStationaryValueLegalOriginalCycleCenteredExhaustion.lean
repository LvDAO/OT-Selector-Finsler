import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalRelativeCycleSelector

/-! Countable centered-cell and positive-threshold exhaustion of actual original cycles. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {q : ℕ}

/-- Every finite pair of original edges fits in a member of one countable
family of centered Ioc spatial boxes. -/
theorem exists_centered_originalCompleteGridCell
    (e f : LegalMarkedPhysicalEdge q) :
    ∃ n : ℕ, e ∈ originalCompleteGridCell q (2 * ((n : ℝ) + 1))
        (fun _ ↦ -((n : ℝ) + 1)) 0 ∧
      f ∈ originalCompleteGridCell q (2 * ((n : ℝ) + 1))
        (fun _ ↦ -((n : ℝ) + 1)) 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (max ‖e.1.1‖ ‖e.2.1‖) (max ‖f.1.1‖ ‖f.2.1‖))
  have hpoint (x : Fin q → ℝ) (hx : ‖x‖ ≤
      max (max ‖e.1.1‖ ‖e.2.1‖) (max ‖f.1.1‖ ‖f.2.1‖)) :
      x ∈ cavityGridCube (Fin q) (2 * ((n : ℝ) + 1))
        ((0 : CavityGridLattice (Fin q) (2 * ((n : ℝ) + 1))) +ᵥ
          (fun _ : Fin q ↦ -((n : ℝ) + 1))) := by
    simp only [zero_vadd]
    intro i _
    have hi : |x i| < (n : ℝ) :=
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i : |x i| ≤ ‖x‖)
        |>.trans_lt (hx.trans_lt hn)
    change 0 < x i - -((n : ℝ) + 1) ∧
      x i - -((n : ℝ) + 1) ≤ 2 * ((n : ℝ) + 1)
    constructor <;> linarith [neg_lt_of_abs_lt hi, lt_of_abs_lt hi]
  refine ⟨n, ⟨hpoint e.1.1 ?_, hpoint e.2.1 ?_⟩,
    ⟨hpoint f.1.1 ?_, hpoint f.2.1 ?_⟩⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- Moving the root to a literal cell base places its two endpoints in the
same reference cell, preserving the original Ioc boundary convention. -/
theorem originalCompleteGridCell_reroot_origin_iff
    (ell : ℝ) (b : Fin q → ℝ) (e : LegalMarkedPhysicalEdge q) :
    physicalSceneEdgeReroot b e ∈ originalCompleteGridCell q ell 0 0 ↔
      e ∈ originalCompleteGridCell q ell b 0 := by
  change ((e.1.1 - b) - ((0 : CavityGridLattice (Fin q) ell) +ᵥ (0 : Fin q → ℝ))
      ∈ cavityGridPhaseCell (Fin q) ell ∧
    (e.2.1 - b) - ((0 : CavityGridLattice (Fin q) ell) +ᵥ (0 : Fin q → ℝ))
      ∈ cavityGridPhaseCell (Fin q) ell) ↔
    (e.1.1 - ((0 : CavityGridLattice (Fin q) ell) +ᵥ b) ∈ cavityGridPhaseCell (Fin q) ell ∧
      e.2.1 - ((0 : CavityGridLattice (Fin q) ell) +ᵥ b) ∈ cavityGridPhaseCell (Fin q) ell)
  simp only [zero_vadd, sub_zero]

/-- Vanishing of every constructed positive-gain cell event implies the
global almost-sure legal two-cycle inequality for all actual occupied edges.
Only countably many centered boxes, roots and positive thresholds are used. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalTwoCycle_of_origin_inactive
    {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    {probe : ℝ → ℝ → ℝ} (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry probe)) (t : ℝ)
    (hInactive : ∀ ell : ℝ, 0 < ell → ∀ ε : ℝ, 0 < ε →
      ∀ S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε,
        (M.law : Measure (LegalMarkedOptimalInputScene q)) S.active = 0) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
        ∀ f ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
          e.1.2 < f.2.2 → f.1.2 < e.2.2 →
            originalWeightedEdgeCost kin probe t e + originalWeightedEdgeCost kin probe t f ≤
              originalWeightedEdgeCost kin probe t (e.1, f.2) +
                originalWeightedEdgeCost kin probe t (f.1, e.2) := by
  let c := originalWeightedEdgeCost kin probe t
  let ell : ℕ → ℝ := fun n ↦ 2 * ((n : ℝ) + 1)
  let ε : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  let b : ℕ → Fin q → ℝ := fun n _ ↦ -((n : ℝ) + 1)
  have hc : Measurable c := measurable_originalWeightedEdgeCost kin hk probe hg t
  let S : ∀ n m : ℕ, OriginalOriginCycleSelector q c (ell n) (ε m) := fun n m ↦
    Classical.choice (exists_originalOriginCycleSelector q c hc (ell n) (ε m))
  have hnull (n m : ℕ) : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      legalMarkedInputSceneReroot q (b n) s ∉ (S n m).active := by
    have he : (M.law : Measure (LegalMarkedOptimalInputScene q)) (S n m).active = 0 :=
      hInactive (ell n) (by dsimp [ell]; positivity) (ε m) (by dsimp [ε]; positivity) (S n m)
    have hbase : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
        s ∉ (S n m).active := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_mem_eq] using he
    exact (M.stationary (b n)).quasiMeasurePreserving.ae hbase
  have hall : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ n m : ℕ, legalMarkedInputSceneReroot q (b n) s ∉ (S n m).active :=
    ae_all_iff.mpr (fun n ↦ ae_all_iff.mpr (hnull n))
  filter_upwards [M.full_matching, hall] with s hs hnone
  intro e he f hf hcross₁ hcross₂
  by_cases hef : e = f
  · subst f
    simp only [Prod.eta, le_refl]
  by_contra hle
  have hbad : 0 < c e + c f - c (e.1, f.2) - c (f.1, e.2) := by
    dsimp only [c]
    linarith
  obtain ⟨n, hen, hfn⟩ := exists_centered_originalCompleteGridCell e f
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hbad
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have hsupp (a : LegalMarkedPhysicalEdge q)
      (ha : a ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support) :
      physicalSceneEdgeReroot (b n) a ∈
        ((legalMarkedInputSceneReroot q (b n) s).1.1 : Measure (LegalMarkedPhysicalEdge q)).support := by
    apply (mem_support_mapHomeomorph_iff_of_legalCounting (0 : LegalMarkedPhysicalEdge q)
      (physicalSceneEdgeReroot (b n)) s.1.1 hcount _).mpr
    simpa only [Homeomorph.symm_apply_apply] using ha
  apply hnone n m
  apply (S n m).active_of_witness _ (hs.reroot (b n))
  refine ⟨physicalSceneEdgeReroot (b n) e, hsupp e he,
    physicalSceneEdgeReroot (b n) f, hsupp f hf, ?_⟩
  refine ⟨fun h ↦ hef ((physicalSceneEdgeReroot (b n)).injective h),
    (originalCompleteGridCell_reroot_origin_iff (ell n) (b n) e).mpr hen,
    (originalCompleteGridCell_reroot_origin_iff (ell n) (b n) f).mpr hfn,
    hcross₁, hcross₂, ?_⟩
  have hcross (a d : LegalMarkedPhysicalEdge q) :
      ((physicalSceneEdgeReroot (b n) a).1, (physicalSceneEdgeReroot (b n) d).2) =
        physicalSceneEdgeReroot (b n) (a.1, d.2) := rfl
  simp only [c, hcross, originalWeightedEdgeCost_reroot]
  exact hm.le

end OTSelector.Reconstruction

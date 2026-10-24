import OTSelector.Probability.BinomialThinning
import OTSelector.Probability.PoissonRestriction

/-! Exact spatial restriction of the original independently counted iid prefix.
The original binomial count law is thinned algebraically before taking limits. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal unitInterval
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [MeasurableSpace X]

/-- The original finite prefix restriction retains its normalized point law
and the exact mixture of the original count and retention probabilities. -/
theorem map_count_restrictedPrefix (ν : Measure X) [IsProbabilityMeasure ν]
    (κ : Measure ℕ) [IsProbabilityMeasure κ] {S : Set X} (hS : MeasurableSet S) :
    (κ.prod (Measure.infinitePi (fun _ : ℕ ↦ ν))).map
      (restrictedPrefix S) =
      blockDataLaw (restrictedPointLaw ν S)
        (fun m ↦ ∑' n, κ {n} * binomWeight n (restrictionWeight ν S) m) := by
  let P := κ.prod (Measure.infinitePi (fun _ : ℕ ↦ ν))
  let pairMap : X → Bool × X := fun x ↦ (restrictionLabel S x, x)
  have hpairMap : Measurable pairMap :=
    (measurable_restrictionLabel hS).prodMk measurable_id
  let p : Bool → ℝ≥0 := fun b ↦ restrictionWeight ν (restrictionPart S b)
  let laws : Bool → Measure X := fun b ↦ restrictedPointLaw ν (restrictionPart S b)
  have hp : ∑ b, p b = 1 := sum_restrictionWeight ν hS
  have hN : P.map Prod.fst = κ := by
    dsimp only [P]
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hpointSeq : iIndepFun (fun (i : ℕ) (x : ℕ → X) ↦ pairMap (x i))
      (Measure.infinitePi (fun _ : ℕ ↦ ν)) :=
    iIndepFun_infinitePi_apply_comp ν pairMap hpairMap
  have hpair (n : ℕ) : iIndepFun
      (fun i : Fin n ↦ fun z : ℕ × (ℕ → X) ↦ pairMap (z.2 i)) P := by
    exact (iIndepFun_snd_prod
      (ν₁ := κ) (ν₂ := Measure.infinitePi (fun _ : ℕ ↦ ν))
      (Y := fun i x ↦ pairMap (x i))
      (fun i ↦ hpairMap.comp (measurable_pi_apply i)) hpointSeq).precomp
      (g := fun i : Fin n ↦ (i : ℕ)) (fun i j hij ↦ Fin.ext hij)
  have hjoint (i : ℕ) : P.map (fun z ↦ pairMap (z.2 i)) = mixturePointLaw p laws := by
    have hev : P.map (fun z : ℕ × (ℕ → X) ↦ z.2 i) = ν := by
      calc
        _ = (P.map Prod.snd).map (fun x : ℕ → X ↦ x i) :=
          (Measure.map_map (measurable_pi_apply i) measurable_snd).symm
        _ = ν := by
          dsimp only [P]
          rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]
    calc
      _ = (P.map (fun z : ℕ × (ℕ → X) ↦ z.2 i)).map pairMap :=
        (Measure.map_map hpairMap ((measurable_pi_apply i).comp measurable_snd)).symm
      _ = ν.map pairMap := by rw [hev]
      _ = _ := map_restrictionLabel_pair ν hS
  have hindep (n : ℕ) : IndepFun (Prod.fst : ℕ × (ℕ → X) → ℕ)
      (fun z ↦ fun i : Fin n ↦ pairMap (z.2 i)) P :=
    indepFun_prod (X := (id : ℕ → ℕ))
      (Y := fun x : ℕ → X ↦ fun i : Fin n ↦ pairMap (x i)) measurable_id
      (measurable_pi_lambda _ (fun i ↦ hpairMap.comp (measurable_pi_apply (i : ℕ))))
  let Y : ℕ → (ℕ × (ℕ → X)) → BlockData X := fun n z ↦
    blockDataOfPairsGen true (fun i : Fin n ↦ (restrictionLabel S (z.2 i), z.2 i))
  have hY (n : ℕ) : Measurable (Y n) :=
    (measurable_blockDataOfPairsGen true).comp (measurable_pi_lambda _
      (fun i ↦ ((measurable_restrictionLabel hS).comp
        ((measurable_pi_apply (i : ℕ)).comp measurable_snd)).prodMk
        ((measurable_pi_apply (i : ℕ)).comp measurable_snd)))
  have hindepY (n : ℕ) : IndepFun (Prod.fst : ℕ × (ℕ → X) → ℕ) (Y n) P := by
    have h := (hindep n).comp measurable_id (measurable_blockDataOfPairsGen true)
    simpa only [Y, Function.comp_def, id_eq, pairMap] using h
  have hYlaw (n : ℕ) : P.map (Y n) =
      blockDataLaw (restrictedPointLaw ν S) (binomWeight n (restrictionWeight ν S)) := by
    have h := map_blockDataOfPairsGen_law
      (P := P) (w := fun (i : Fin n) z ↦ restrictionLabel S (z.2 i))
      (x := fun (i : Fin n) z ↦ z.2 i)
      (fun i ↦ (measurable_restrictionLabel hS).comp
        ((measurable_pi_apply (i : ℕ)).comp measurable_snd))
      (fun i ↦ (measurable_pi_apply (i : ℕ)).comp measurable_snd) (hpair n)
      p hp laws (fun i ↦ hjoint (i : ℕ)) true
    simpa only [Y, p, laws, restrictionPart, ↓reduceIte] using h
  have hcount := map_count_prefix_gen κ Prod.fst Y hN hY hindepY
  change P.map (fun z ↦ Y z.1 z) = _
  rw [hcount]
  simp_rw [hYlaw]
  exact blockDataLaw_mix_gen (restrictedPointLaw ν S) (fun n ↦ κ {n})
    (fun m ↦ ∑' n, κ {n} * binomWeight n (restrictionWeight ν S) m)
    (fun n ↦ binomWeight n (restrictionWeight ν S)) (fun _ ↦ rfl)

/-- Restricting the original binomial prefix gives the exact original
binomial shape count, including null events and their unused fallback law. -/
theorem map_binomial_restrictedPrefix (ν : Measure X) [IsProbabilityMeasure ν]
    (N : ℕ) (p : I) {S : Set X} (hS : MeasurableSet S) :
    ((ProbabilityTheory.binomial N p).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))).map
      (restrictedPrefix S) =
      blockDataLaw (restrictedPointLaw ν S)
        (binomWeight N (Real.toNNReal (p : ℝ) * restrictionWeight ν S)) := by
  rw [map_count_restrictedPrefix ν _ hS]
  congr 1
  funext m
  simp_rw [binomial_singleton_eq_binomWeight]
  have hw : restrictionWeight ν S ≤ 1 := by
    apply ENNReal.coe_le_coe.mp
    change (((ν S).toNNReal : ℝ≥0∞) ≤ ↑(1 : ℝ≥0))
    rw [ENNReal.coe_toNNReal (measure_ne_top ν S), ENNReal.coe_one]
    simpa only [measure_univ] using measure_mono (μ := ν) (subset_univ S)
  exact binomWeight_compound_nnreal N m (Real.toNNReal (p : ℝ))
    (restrictionWeight ν S) (Real.toNNReal_le_one.mpr p.2.2) hw

end OTSelector.Probability

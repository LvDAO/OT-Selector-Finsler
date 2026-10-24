import OTSelector.Probability.MarkedMixtureThinning
import Mathlib.Probability.ConditionalProbability

/-! Exact finite-prefix restriction laws for arbitrary measurable point sets. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [MeasurableSpace X]

/-- Normalize the original restriction; a null event uses the original law as an
unused probability witness because its Poisson intensity is zero. -/
def restrictedPointLaw (ν : Measure X) (S : Set X) : Measure X :=
  if ν S = 0 then ν else ProbabilityTheory.cond ν S

instance isProbabilityMeasure_restrictedPointLaw (ν : Measure X) [IsProbabilityMeasure ν]
    (S : Set X) : IsProbabilityMeasure (restrictedPointLaw ν S) := by
  classical
  by_cases h : ν S = 0
  · simpa only [restrictedPointLaw, h, ↓reduceIte] using (inferInstance : IsProbabilityMeasure ν)
  · simpa only [restrictedPointLaw, h, ↓reduceIte] using cond_isProbabilityMeasure h

/-- Original restriction is exactly its mass times its conditional point law. -/
theorem measure_smul_restrictedPointLaw (ν : Measure X) [IsProbabilityMeasure ν]
    (S : Set X) : ν S • restrictedPointLaw ν S = ν.restrict S := by
  classical
  by_cases h : ν S = 0
  · simp only [restrictedPointLaw, h, ↓reduceIte, zero_smul]
    exact (Measure.restrict_eq_zero.mpr h).symm
  · simp only [restrictedPointLaw, h, ↓reduceIte, ProbabilityTheory.cond, smul_smul,
      ENNReal.mul_inv_cancel h (measure_ne_top ν S), one_smul]

/-- Original mass as a finite Poisson thinning weight. -/
def restrictionWeight (ν : Measure X) (S : Set X) : ℝ≥0 := (ν S).toNNReal

def restrictionLabel (S : Set X) (x : X) : Bool := by
  classical
  exact if x ∈ S then true else false

theorem measurable_restrictionLabel {S : Set X} (hS : MeasurableSet S) :
    Measurable (restrictionLabel S) :=
  measurable_const.ite hS measurable_const

def restrictionPart (S : Set X) (b : Bool) : Set X := if b then S else Sᶜ

theorem sum_restrictionWeight (ν : Measure X) [IsProbabilityMeasure ν]
    {S : Set X} (hS : MeasurableSet S) :
    (∑ b : Bool, restrictionWeight ν (restrictionPart S b)) = 1 := by
  have h := measure_add_measure_compl hS (μ := ν)
  rw [measure_univ] at h
  simp only [Fintype.sum_bool, restrictionPart, Bool.false_eq_true, ↓reduceIte]
  apply NNReal.eq
  change (ν S).toReal + (ν Sᶜ).toReal = 1
  rw [← ENNReal.toReal_add (measure_ne_top ν S) (measure_ne_top ν Sᶜ), h]
  simp

/-- The actual label and point decompose into their two original restrictions. -/
theorem map_restrictionLabel_pair (ν : Measure X) [IsProbabilityMeasure ν]
    {S : Set X} (hS : MeasurableSet S) :
    ν.map (fun x ↦ (restrictionLabel S x, x)) =
      mixturePointLaw (fun b ↦ restrictionWeight ν (restrictionPart S b))
        (fun b ↦ restrictedPointLaw ν (restrictionPart S b)) := by
  classical
  let f : X → Bool × X := fun x ↦ (restrictionLabel S x, x)
  have hf : Measurable f := (measurable_restrictionLabel hS).prodMk measurable_id
  have htrue : (ν.restrict S).map f = (Measure.dirac true).prod (ν.restrict S) := by
    calc
      _ = (ν.restrict S).map (fun x ↦ (true, x)) :=
        Measure.map_congr (by
          filter_upwards [ae_restrict_mem hS] with x hx
          simp only [f, restrictionLabel, hx, ↓reduceIte])
      _ = _ := map_prodMk_const (ν.restrict S) true
  have hfalse : (ν.restrict Sᶜ).map f = (Measure.dirac false).prod (ν.restrict Sᶜ) := by
    calc
      _ = (ν.restrict Sᶜ).map (fun x ↦ (false, x)) :=
        Measure.map_congr (by
          filter_upwards [ae_restrict_mem hS.compl] with x hx
          simp only [mem_compl_iff] at hx
          simp only [f, restrictionLabel, hx, ↓reduceIte])
      _ = _ := map_prodMk_const (ν.restrict Sᶜ) false
  change ν.map f = _
  conv_lhs => rw [← Measure.restrict_add_restrict_compl hS (μ := ν)]
  rw [Measure.map_add _ _ hf, htrue, hfalse]
  simp only [mixturePointLaw, Fintype.sum_bool, restrictionPart, Bool.false_eq_true, ↓reduceIte]
  have hmass (T : Set X) : (restrictionWeight ν T : ℝ≥0∞) = ν T :=
    ENNReal.coe_toNNReal (measure_ne_top ν T)
  simp_rw [hmass, ← Measure.prod_smul_right, measure_smul_restrictedPointLaw]


/-- Enumerate precisely the original observations in the selected point set. -/
def restrictedPrefix (S : Set X) (z : ℕ × (ℕ → X)) : BlockData X :=
  prefixBlockDataGen (Prod.fst : ℕ × (ℕ → X) → ℕ)
    (fun i z ↦ restrictionLabel S (z.2 i)) (fun i z ↦ z.2 i) true z

/-- Exact law of an arbitrary measurable restriction of a Poissonized iid
prefix. No independent unused tail is attributed to the selected cloud. -/
theorem map_restrictedPrefix (ν : Measure X) [IsProbabilityMeasure ν]
    (r : ℝ≥0) {S : Set X} (hS : MeasurableSet S) :
    ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))).map
      (restrictedPrefix S) =
      blockDataLaw (restrictedPointLaw ν S)
        (fun n ↦ poissonMeasure (r * restrictionWeight ν S) {n}) := by
  let P := (poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))
  let pairMap : X → Bool × X := fun x ↦ (restrictionLabel S x, x)
  have hpairMap : Measurable pairMap :=
    (measurable_restrictionLabel hS).prodMk measurable_id
  let p : Bool → ℝ≥0 := fun b ↦ restrictionWeight ν (restrictionPart S b)
  let laws : Bool → Measure X := fun b ↦ restrictedPointLaw ν (restrictionPart S b)
  have hp : ∑ b, p b = 1 := sum_restrictionWeight ν hS
  have hN : P.map Prod.fst = poissonMeasure r := by
    dsimp only [P]
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hpointSeq : iIndepFun (fun (i : ℕ) (x : ℕ → X) ↦ pairMap (x i))
      (Measure.infinitePi (fun _ : ℕ ↦ ν)) :=
    iIndepFun_infinitePi_apply_comp ν pairMap hpairMap
  have hpair (n : ℕ) : iIndepFun
      (fun i : Fin n ↦ fun z : ℕ × (ℕ → X) ↦ pairMap (z.2 i)) P := by
    exact (iIndepFun_snd_prod
      (ν₁ := poissonMeasure r) (ν₂ := Measure.infinitePi (fun _ : ℕ ↦ ν))
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
  have h := map_poisson_blockDataOfPairsGen (P := P) r Prod.fst
    (fun i z ↦ restrictionLabel S (z.2 i)) (fun i z ↦ z.2 i) p hp laws hN hpair
    (fun i ↦ (measurable_restrictionLabel hS).comp
      ((measurable_pi_apply i).comp measurable_snd))
    (fun i ↦ (measurable_pi_apply i).comp measurable_snd) hjoint hindep true
  unfold restrictedPrefix
  simpa only [p, laws, restrictionPart, ↓reduceIte, P] using h

variable {Y : Type*} [MeasurableSpace Y]

/-- Conditioning after a measurable coordinate map is the pushforward of the
original law conditioned on the preimage. Null shapes use the same fallback. -/
theorem restrictedPointLaw_map (ν : Measure X) [IsProbabilityMeasure ν]
    {f : X → Y} (hf : Measurable f) {S : Set Y} (hS : MeasurableSet S) :
    restrictedPointLaw (ν.map f) S = (restrictedPointLaw ν (f ⁻¹' S)).map f := by
  unfold restrictedPointLaw
  rw [Measure.map_apply hf hS]
  by_cases h : ν (f ⁻¹' S) = 0
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, ProbabilityTheory.cond]
    rw [Measure.map_apply hf hS, Measure.restrict_map hf hS, Measure.map_smul]


/-- Selecting the used observations in any measurable point set is measurable. -/
theorem measurable_restrictedPrefix {S : Set X} (hS : MeasurableSet S) :
    Measurable (restrictedPrefix S) := by
  let F : (n : ℕ) → (ℕ → X) → BlockData X := fun n x ↦
    blockDataOfPairsGen true (fun i : Fin n ↦ (restrictionLabel S (x i), x i))
  have hF (n : ℕ) : Measurable (F n) := by
    apply (measurable_blockDataOfPairsGen (Pos := X) true).comp
    exact measurable_pi_lambda _ fun i ↦
      ((measurable_restrictionLabel hS).comp (measurable_pi_apply (i : ℕ))).prodMk
        (measurable_pi_apply (i : ℕ))
  intro U hU
  have hpre : restrictedPrefix S ⁻¹' U =
      ⋃ n : ℕ, {z : ℕ × (ℕ → X) | z.1 = n} ∩ (fun z ↦ F n z.2) ⁻¹' U := by
    ext z
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨z.1, rfl, h⟩
    · rintro ⟨n, hn, h⟩
      subst n
      exact h
  rw [hpre]
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_eq_fun measurable_fst measurable_const).inter
      (((hF n).comp measurable_snd) hU)

end OTSelector.Probability

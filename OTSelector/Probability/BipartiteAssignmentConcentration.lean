import OTSelector.Probability.AssignmentPressureVariance

/-!
# Assignment concentration on the original two-color sample space

Independence within each original color and independence of the two arrays give
exactly the product law of paired observations. The actual assignment minimum
therefore satisfies the bounded-difference variance and deviation estimates on
its original probability space. No distinctness or optimizer selection is used.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Probability

variable {S T Ω : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace Ω]

/-- Pairing the two original iid arrays preserves their actual product law. -/
theorem measurePreserving_bipartiteIidPairs
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ] (ν : Measure T) [IsProbabilityMeasure ν]
    {n : ℕ} (X : Fin n → Ω → S) (Y : Fin n → Ω → T)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ i, P.map (Y i) = ν)
    (hXY : IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) P) :
    MeasurePreserving (fun ω i ↦ (X i ω, Y i ω)) P
      (Measure.pi fun _ : Fin n ↦ μ.prod ν) := by
  have hmX : Measurable (fun ω i ↦ X i ω) := measurable_pi_lambda _ hX
  have hmY : Measurable (fun ω i ↦ Y i ω) := measurable_pi_lambda _ hY
  have hlX : P.map (fun ω i ↦ X i ω) = Measure.pi (fun _ : Fin n ↦ μ) := by
    rw [hXi.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable)]
    simp_rw [hXlaw]
  have hlY : P.map (fun ω i ↦ Y i ω) = Measure.pi (fun _ : Fin n ↦ ν) := by
    rw [hYi.map_fun_eq_pi_map (fun i ↦ (hY i).aemeasurable)]
    simp_rw [hYlaw]
  have hjoint := hXY.map_prod_eq_prod_map_map hmX.aemeasurable hmY.aemeasurable
  rw [hlX, hlY] at hjoint
  have hp : MeasurePreserving (fun ω ↦ ((fun i ↦ X i ω), (fun i ↦ Y i ω))) P
      ((Measure.pi fun _ : Fin n ↦ μ).prod (Measure.pi fun _ : Fin n ↦ ν)) :=
    ⟨hmX.prodMk hmY, hjoint⟩
  exact ((measurePreserving_arrowProdEquivProdArrow S T (Fin n)
    (fun _ ↦ μ) (fun _ ↦ ν)).symm
      (MeasurableEquiv.arrowProdEquivProdArrow S T (Fin n))).comp hp

/-- Both paired iid facts follow from the original two-color independence assumptions. -/
theorem bipartiteIidPairs_indep_law
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ] (ν : Measure T) [IsProbabilityMeasure ν]
    {n : ℕ} (X : Fin n → Ω → S) (Y : Fin n → Ω → T)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ i, P.map (Y i) = ν)
    (hXY : IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) P) :
    iIndepFun (fun i ω ↦ (X i ω, Y i ω)) P ∧
      ∀ i, P.map (fun ω ↦ (X i ω, Y i ω)) = μ.prod ν := by
  have hp := measurePreserving_bipartiteIidPairs P μ ν X Y hX hY hXi hYi hXlaw hYlaw hXY
  have hlaw (i : Fin n) : P.map (fun ω ↦ (X i ω, Y i ω)) = μ.prod ν :=
    ((measurePreserving_eval (fun _ : Fin n ↦ μ.prod ν) i).comp hp).map_eq
  refine ⟨(iIndepFun_iff_map_fun_eq_pi_map
    (fun i ↦ ((hX i).prodMk (hY i)).aemeasurable)).mpr ?_, hlaw⟩
  simp_rw [hlaw]
  exact hp.map_eq

/-- The genuine pressure variance bound under the original independent iid colors. -/
theorem variance_bipartiteAssignmentMean_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ] (ν : Measure T) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → S) (Y : Fin n → Ω → T)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ i, P.map (Y i) = ν)
    (hXY : IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) P)
    {c : S → T → ℝ} (hc : Measurable (Function.uncurry c))
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x y, |c x y| ≤ B) :
    variance (fun ω ↦ sampleAssignmentMean c (fun i ↦ (X i ω, Y i ω))) P ≤
      16 * B ^ 2 / (n : ℝ) := by
  obtain ⟨hi, hlaw⟩ := bipartiteIidPairs_indep_law P μ ν X Y hX hY hXi hYi hXlaw hYlaw hXY
  exact variance_sampleAssignmentMean_iid_le P (μ.prod ν) hn _
    (fun i ↦ (hX i).prodMk (hY i)) hi hlaw hc hB hbound

/-- An explicit centered probability bound for the actual original bipartite minimum. -/
theorem deviation_bipartiteAssignmentMean_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ] (ν : Measure T) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → S) (Y : Fin n → Ω → T)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ i, P.map (Y i) = ν)
    (hXY : IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) P)
    {c : S → T → ℝ} (hc : Measurable (Function.uncurry c))
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x y, |c x y| ≤ B) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |sampleAssignmentMean c (fun i ↦ (X i ω, Y i ω)) -
      ∫ ω', sampleAssignmentMean c (fun i ↦ (X i ω', Y i ω')) ∂P|} ≤
        (16 * B ^ 2 / (n : ℝ)) / ε ^ 2 := by
  obtain ⟨hi, hlaw⟩ := bipartiteIidPairs_indep_law P μ ν X Y hX hY hXi hYi hXlaw hYlaw hXY
  exact deviation_sampleAssignmentMean_iid_le P (μ.prod ν) hn _
    (fun i ↦ (hX i).prodMk (hY i)) hi hlaw hc hB hbound hε

end OTSelector.Probability

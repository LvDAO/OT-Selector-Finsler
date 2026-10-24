import OTSelector.Limit.FinslerCanonicalTileData

/-!
# The canonical two-colour sample is an actual iid sampling model

The existing `canonicalOmega`, `canonicalLaw`, `canonicalX` and `canonicalY`
use two independent finite product populations. This module proves independence
within each colour and independence of the two whole arrays, complementing the
existing coordinate measurability and marginal-law theorems.

Every conclusion holds for arbitrary probability measures on a measurable space.
In particular this supplies the iid sampling hypotheses without identifying a
fixed finite cloud's empirical law with its population law.
-/

open MeasureTheory ProbabilityTheory

namespace OTSelector.Probability

variable {M : Type*} [MeasurableSpace M]

/-- The whole source word has the finite product source-population law. -/
theorem canonicalLaw_map_sourceArray (μ ν : ProbabilityMeasure M) (n : ℕ) :
    (canonicalLaw μ ν n).map (fun ξ i ↦ canonicalX n i ξ) =
      Measure.pi (fun _ : Fin (n + 1) ↦ (μ : Measure M)) := by
  change ((Measure.pi (fun _ : Fin (n + 1) ↦ (μ : Measure M))).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M)))).map Prod.fst = _
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The whole target word has the finite product target-population law. -/
theorem canonicalLaw_map_targetArray (μ ν : ProbabilityMeasure M) (n : ℕ) :
    (canonicalLaw μ ν n).map (fun ξ i ↦ canonicalY n i ξ) =
      Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M)) := by
  change ((Measure.pi (fun _ : Fin (n + 1) ↦ (μ : Measure M))).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M)))).map Prod.snd = _
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- The source coordinates of the canonical sample are independent. -/
theorem iIndepFun_canonicalX (μ ν : ProbabilityMeasure M) (n : ℕ) :
    iIndepFun (canonicalX (M := M) n) (canonicalLaw μ ν n) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i ↦ (measurable_canonicalX n i).aemeasurable)).mpr
  simp_rw [canonicalLaw_map_canonicalX]
  exact canonicalLaw_map_sourceArray μ ν n

/-- The target coordinates of the canonical sample are independent. -/
theorem iIndepFun_canonicalY (μ ν : ProbabilityMeasure M) (n : ℕ) :
    iIndepFun (canonicalY (M := M) n) (canonicalLaw μ ν n) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i ↦ (measurable_canonicalY n i).aemeasurable)).mpr
  simp_rw [canonicalLaw_map_canonicalY]
  exact canonicalLaw_map_targetArray μ ν n

/-- The two complete colour arrays are independent under the canonical sample law. -/
theorem indepFun_canonicalArrays (μ ν : ProbabilityMeasure M) (n : ℕ) :
    IndepFun (fun ξ i ↦ canonicalX n i ξ) (fun ξ j ↦ canonicalY n j ξ)
      (canonicalLaw μ ν n) := by
  change IndepFun (fun ξ : canonicalOmega M n ↦ ξ.1) (fun ξ ↦ ξ.2)
    ((Measure.pi (fun _ : Fin (n + 1) ↦ (μ : Measure M))).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))))
  exact indepFun_prod measurable_id measurable_id

/-- The independence and population-law hypotheses required by iid selector
interfaces are produced together on the canonical two-colour sample space. -/
theorem canonicalLaw_iid_sampling (μ ν : ProbabilityMeasure M) (n : ℕ) :
    iIndepFun (canonicalX (M := M) n) (canonicalLaw μ ν n) ∧
    iIndepFun (canonicalY (M := M) n) (canonicalLaw μ ν n) ∧
    IndepFun (fun ξ i ↦ canonicalX n i ξ) (fun ξ j ↦ canonicalY n j ξ)
      (canonicalLaw μ ν n) ∧
    (∀ i, (canonicalLaw μ ν n).map (canonicalX n i) = (μ : Measure M)) ∧
    (∀ j, (canonicalLaw μ ν n).map (canonicalY n j) = (ν : Measure M)) :=
  ⟨iIndepFun_canonicalX μ ν n, iIndepFun_canonicalY μ ν n,
    indepFun_canonicalArrays μ ν n, canonicalLaw_map_canonicalX μ ν n,
    canonicalLaw_map_canonicalY μ ν n⟩

end OTSelector.Probability

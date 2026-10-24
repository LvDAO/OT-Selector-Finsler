import OTSelector.Probability.Dirichlet.CavitySplit
import OTSelector.Probability.Dirichlet.CavitySuccess
import OTSelector.Probability.CavityDirichletMoments
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Exact original iid laws for retained subsets

A fixed actual source subset is enumerated as the retained cavity input. Its complement
keeps its original labels. Splitting the original finite iid array gives exactly the
product of these laws; the candidate's cavity matrix is the ordinary retained-input matrix.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {n m : ℕ} {S : Type*} [MeasurableSpace S]





@[simp]
theorem cavitySubsetSplit_snd (I : {I : Finset (Fin n) // I.card = m})
    (x : Fin n → S) (k : {k : Fin n // k ∉ I.1}) :
    (cavitySubsetSplit I x).2 k = x k := rfl









end OTSelector.Probability

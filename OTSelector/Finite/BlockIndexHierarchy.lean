import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Finite.BlockIndexHierarchy

## Lemma skeleton

* **Conditions:** Natural grid sizes, levels k≤l≤J and finitely many coordinate indices.

* **Objects:** Dyadic quotient labels of finite grid indices; refinement and root/self labels.

* **Proof detail:** Divide each coordinate by 2^(J-k). Repeated natural division composes after factoring powers of two; bounds force the root quotient to be zero.

## Mathematical sources

- [Thomas W. Judson, Abstract Algebra: Theory and Applications (author online edition)](https://twjudson.github.io/aata-files/aata-html/integers-section-division-algorithm.html): Section 2.2, Theorem 2.2.1 (Division Algorithm).
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): The padded finite-type grid is a local coding construction using the division algorithm, not a named theorem in the books.
-/

/-!
# Dyadic coarsening of a finite block grid

For the multi-scale block comparison, a cube is tiled into `m^q` blocks indexed
by `Fin q → Fin m`.  The blocks are grouped into dyadic cells by dividing each
index coordinate by a power of two.  With total depth `J`, level `k` uses the
divisor `2^(J-k)`: level `0` is the root and level `J` is the block grid.  The
cells at a finer level refine those at a coarser level, which is the nestedness
input of the hierarchical matching bound.

The cell type is `Fin q → Fin (m+1)` at every level.  Values above `m-1` are
unused padding labels; the partition counts of those labels are zero.
-/

namespace OTSelector

/-- The level-`k` dyadic cell of a block index. -/
def blockCell (q m J k : ℕ) (b : Fin q → Fin m) : Fin q → Fin (m + 1) :=
  fun l => ⟨(b l).val / 2 ^ (J - k),
    Nat.lt_succ_of_le (le_trans (Nat.div_le_self _ _) (Nat.le_of_lt (b l).isLt))⟩

/-- Nestedness: a finer level determines every coarser level. -/
theorem blockCell_nested {q m J k l : ℕ} (hkl : k ≤ l) (hlJ : l ≤ J)
    (b b' : Fin q → Fin m)
    (h : blockCell q m J l b = blockCell q m J l b') :
    blockCell q m J k b = blockCell q m J k b' := by
  funext i
  have hi := congrFun h i
  simp only [blockCell, Fin.mk.injEq] at hi ⊢
  have hpow : (2 : ℕ) ^ (J - l) * 2 ^ (l - k) = 2 ^ (J - k) := by
    rw [← pow_add]
    congr 1
    omega
  have hdiv : (b i).val / 2 ^ (J - k) =
      ((b i).val / 2 ^ (J - l)) / 2 ^ (l - k) := by
    rw [Nat.div_div_eq_div_mul, hpow]
  have hdiv' : (b' i).val / 2 ^ (J - k) =
      ((b' i).val / 2 ^ (J - l)) / 2 ^ (l - k) := by
    rw [Nat.div_div_eq_div_mul, hpow]
  rw [hdiv, hdiv', hi]

/-- At the leaf level the block index is recovered (up to the padding
embedding). -/
theorem blockCell_self (q m : ℕ) (b : Fin q → Fin m) :
    blockCell q m m m b =
      fun i => ⟨(b i).val, Nat.lt_succ_of_lt (b i).isLt⟩ := by
  funext i
  simp only [blockCell, Nat.sub_self, pow_zero, Nat.div_one]

/-- At depth `J` with `m ≤ 2^J` the root cell is unique. -/
theorem blockCell_root_eq {q m J : ℕ} (hJ : m ≤ 2 ^ J) (b b' : Fin q → Fin m) :
    blockCell q m J 0 b = blockCell q m J 0 b' := by
  funext i
  simp only [blockCell, Fin.mk.injEq, Nat.sub_zero]
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le (b i).isLt hJ),
    Nat.div_eq_of_lt (lt_of_lt_of_le (b' i).isLt hJ)]

end OTSelector

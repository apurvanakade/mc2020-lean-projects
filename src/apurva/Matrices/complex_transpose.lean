import data.complex.basic 
import data.fintype.basic 
import data.matrix.basic
import linear_algebra.determinant
import linear_algebra.nonsingular_inverse
import tactic 

noncomputable theory 
open_locale classical
open_locale matrix

universes u u'
variables {m n l : Type u} [fintype m] [fintype n] [fintype l]

local notation `Euc` := (n → ℂ)

namespace matrix
/-- Complex conjugate of a vector.-/
def conj (M : matrix m n ℂ) : matrix m n ℂ := 
λ i j, complex.conj (M i j)

def complex_transpose (M : matrix m n ℂ) : matrix n m ℂ :=
M.transpose.conj
end matrix

section complex_transpose
/--
  Tell `simp` what the entries are in a transposed matrix.
-/
@[simp] lemma complex_transpose_val (M : matrix m n ℂ) (i j) : M.complex_transpose j i = complex.conj (M i j) := rfl

@[simp] lemma complex_transpose_transpose (M : matrix m n ℂ) :
  M.complex_transpose.complex_transpose = M :=
by sorry

@[simp] lemma complex_transpose_zero [has_zero ℂ] : (0 : matrix m n ℂ).complex_transpose = 0 :=
by sorry

@[simp] lemma complex_transpose_one [decidable_eq n] : (1 : matrix n n ℂ).complex_transpose = 1 := sorry

@[simp] lemma complex_transpose_add (M : matrix m n ℂ) (N : matrix m n ℂ) :
  (M + N).complex_transpose = M.complex_transpose + N.complex_transpose  :=
sorry

@[simp] lemma complex_transpose_sub [add_group ℂ] (M : matrix m n ℂ) (N : matrix m n ℂ) :
  (M - N).complex_transpose = M.complex_transpose - N.complex_transpose  :=
sorry

@[simp] lemma complex_transpose_mul [comm_semiring ℂ] (M : matrix m n ℂ) (N : matrix n l ℂ) :
  (M ⬝ N).complex_transpose = N.complex_transpose ⬝ M.complex_transpose  :=
sorry

@[simp] lemma complex_transpose_smul (c : ℂ) (M : matrix m n ℂ) :
  (c • M).complex_transpose = complex.conj c • M.complex_transpose :=
sorry

@[simp] lemma complex_transpose_neg [has_neg ℂ] (M : matrix m n ℂ) :
  (- M).complex_transpose = - M.complex_transpose  :=
sorry

end complex_transpose
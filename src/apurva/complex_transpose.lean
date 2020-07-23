import data.complex.basic 
import data.fintype.basic 
import data.matrix.basic
import linear_algebra.determinant
import linear_algebra.nonsingular_inverse
import tactic 

noncomputable theory 
open_locale classical
open_locale matrix
open_locale big_operators

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
open complex matrix
/--
  Tell `simp` what the entries are in a transposed matrix.
-/
@[simp] lemma complex_transpose_val (M : matrix m n ℂ) (i j) : M.complex_transpose j i = complex.conj (M i j) := rfl

@[simp] lemma complex_transpose_transpose (M : matrix m n ℂ) :
  M.complex_transpose.complex_transpose = M :=
by ext; simp

@[simp] lemma complex_transpose_zero : (0 : matrix m n ℂ).complex_transpose = 0 :=
by ext; simp

@[simp] lemma complex_transpose_one [decidable_eq n] : (1 : matrix n n ℂ).complex_transpose = 1 := 
by ext; simp [matrix.one_val]; split_ifs; simp; cc

@[simp] lemma complex_transpose_add (M : matrix m n ℂ) (N : matrix m n ℂ) :
  (M + N).complex_transpose = M.complex_transpose + N.complex_transpose  :=
by ext; simp

@[simp] lemma complex_transpose_neg (M : matrix m n ℂ) :
  (- M).complex_transpose = - M.complex_transpose  :=
by ext; simp 

@[simp] lemma complex_transpose_sub (M : matrix m n ℂ) (N : matrix m n ℂ) :
  (M - N).complex_transpose = M.complex_transpose - N.complex_transpose  :=
by ext; simp

@[simp] lemma complex_transpose_mul (M : matrix m n ℂ) (N : matrix n l ℂ) :
  (M ⬝ N).complex_transpose = N.complex_transpose ⬝ M.complex_transpose  :=
begin
  ext; simp, delta matrix.mul, delta matrix.dot_product, simp,
  -- rw add_monoid_hom.map_sum, -- I think this would work if re were a bundled hom
  {sorry}, 
  {sorry}
end

@[simp] lemma complex_transpose_smul (c : ℂ) (M : matrix m n ℂ) :
  (c • M).complex_transpose = complex.conj c • M.complex_transpose :=
by ext; simp



lemma det_of_complex_transpose {A : matrix n n ℂ} : 
A.complex_transpose.det = complex.conj (A.det) :=
  sorry


end complex_transpose
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

  Compare with `mul_val`, `diagonal_val_eq`, etc.
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



section unitary 

def matrix.unitary (A : matrix n n ℂ) := 
  A ⬝ (A.complex_transpose) = 1

lemma unit_det_of_unitary {A : matrix n n ℂ} (hu : A.unitary) : is_unit A.det :=
begin 
  have := matrix.det_mul A A.complex_transpose,
  unfold matrix.unitary at hu,
  rw [hu, matrix.det_one] at this,
  exact is_unit_of_mul_eq_one (matrix.det A) (matrix.complex_transpose A).det (eq.symm this),
end 

lemma unit_of_unitary {A : matrix n n ℂ} (hu : A.unitary) : is_unit A :=
  (matrix.is_unit_iff_is_unit_det A).mpr (unit_det_of_unitary hu)

/--------------------------------------------------------------
-- I really need to say that A⁻¹ = A.complex transpose and 
-- A.complex_transpose ⬝ A = 1
--------------------------------------------------------------/

lemma unit_of_complex_transpose {A : matrix n n ℂ} (hu : A.unitary) : is_unit A.complex_transpose :=
  sorry

lemma unitary.has_mul {A B : matrix n n ℂ} (hA : A.unitary) (hB : B.unitary) :
  (A ⬝ B).unitary := 
begin 
unfold matrix.unitary at *,
rw complex_transpose_mul,
calc A ⬝ B ⬝ (B.complex_transpose ⬝ A.complex_transpose) 
    = A ⬝ (B ⬝ (B.complex_transpose ⬝ A.complex_transpose)) : by rw matrix.mul_assoc
... = A ⬝ ((B ⬝ B.complex_transpose) ⬝ A.complex_transpose) : by rw matrix.mul_assoc
... = 1 : by {simp only [hB, matrix.one_mul, hA]},
end 

lemma unitary.has_one : (1 : matrix n n ℂ).unitary := 
begin 
  unfold matrix.unitary,
  simp,
end 

end unitary 


section normal
def normal (A : matrix n n ℂ) := 
  A * A.complex_transpose = A.complex_transpose * A



/--

todo later: 

@[ext]
structure unitary_matrices (n : Type u) [fintype n]:= 
(val : matrix n n ℂ)
(is_unitary : val.unitary)


instance : group (unitary_matrices n) := 
{ mul := λ A B, 
  { val := A.val ⬝ B.val,
  is_unitary := unitary.has_mul A.is_unitary B.is_unitary},
  mul_assoc := λ A B C, sorry ,
  one := { val := (1 : matrix n n ℂ),
    is_unitary := unitary.has_one},
  one_mul := λ A, by { },
  mul_one := sorry,
  inv := sorry,
  mul_left_inv := sorry}



section symmetric 

end symmetric 

section skew_symmtric 

end skew_symmtric 


section hermitian 
def hermitian (A : matrix n n ℂ) := 
  A = A.complex_transpose
end hermitian 


section anti_hermitian 

end anti_hermitian 
-- structure units (ℂ : Type u) [monoid ℂ] :=
-- (val : ℂ)
-- (inv : ℂ)
-- (val_inv : val * inv = 1)
-- (inv_val : inv * val = 1)

theorem normal_of_hermitian {A : matrix n n ℂ} (hh : hermitian A) : normal A := 
  by {unfold normal, unfold hermitian at hh, rw ←hh,}

theorem normal_of_unitary {A : matrix n n ℂ} (hu : A.unitary) : normal A := 
sorry
end normal 


-/
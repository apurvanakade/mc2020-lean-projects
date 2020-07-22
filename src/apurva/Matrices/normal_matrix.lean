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
  (M ⬝ N).complex_transpose = N.complex_transpose ⬝ Mᵀ  :=
sorry

@[simp] lemma complex_transpose_smul (c : ℂ) (M : matrix m n ℂ) :
  (c • M).complex_transpose = complex.conj c • M.complex_transpose :=
sorry

@[simp] lemma complex_transpose_neg [has_neg ℂ] (M : matrix m n ℂ) :
  (- M).complex_transpose = - M.complex_transpose  :=
sorry

end complex_transpose



section unitary 

def unitary (A : matrix n n ℂ) := 
  A ⬝ (A.complex_transpose) = 1

lemma unit_det_of_unitary {A : matrix n n ℂ} (hu : unitary A) : is_unit A.det :=
begin 
  have := matrix.det_mul A A.complex_transpose,
  unfold unitary at hu,
  rw [hu, matrix.det_one] at this,
  exact is_unit_of_mul_eq_one (matrix.det A) (matrix.complex_transpose A).det (eq.symm this),
end 

lemma unit_of_unitary {A : matrix n n ℂ} (hu : unitary A) : is_unit A :=
  (matrix.is_unit_iff_is_unit_det A).mpr (unit_det_of_unitary hu)

lemma unit_of_complex_transpose_of_unitary {A : matrix n n ℂ} (hu : unitary A) : is_unit A.complex_transpose :=
  sorry

example {A : matrix n n ℂ} (hu : unitary A) : A⁻¹ = A.complex_transpose := 
begin
  have h1 := unit_of_unitary hu,
  have h2 := unit_of_complex_transpose_of_unitary hu,
  unfold unitary at hu,
  --sorry
end 


example {n : Type u}
  [fintype n]
  {A : matrix n n ℂ}
  (this : is_unit A)
  (hu : A ⬝ A.complex_transpose = 1) :
  A⁻¹ = A.complex_transpose :=
begin
  suggest
end

-- what would be the correct way to define this?
structure unitary_matrices (n : Type u) [fintype n]:= 
(val : matrix n n ℂ)
(is_unitary : unitary val)

instance : group (unitary_matrices n) := 
{ mul := sorry,
  mul_assoc := sorry,
  one := sorry,
  one_mul := sorry,
  mul_one := sorry,
  inv := sorry,
  mul_left_inv := sorry}

end unitary 


section hermitian 
def hermitian (A : matrix n n ℂ) := 
  A = A.complex_transpose
end hermitian 

section normal
def normal (A : matrix n n ℂ) := 
  A * A.complex_transpose = A.complex_transpose * A

theorem normal_of_hermitian {A : matrix n n ℂ} (hh : hermitian A) : normal A := 
  by {unfold normal, unfold hermitian at hh, rw ←hh,}

theorem normal_of_unitary {A : matrix n n ℂ} (hu : unitary A) : normal A := 
sorry
end normal 

section symmetric 

end symmetric 

section skew_symmtric 

end skew_symmtric 

section anti_hermitian 

end anti_hermitian 
-- structure units (ℂ : Type u) [monoid ℂ] :=
-- (val : ℂ)
-- (inv : ℂ)
-- (val_inv : val * inv = 1)
-- (inv_val : inv * val = 1)


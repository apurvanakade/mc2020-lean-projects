import data.complex.basic 
import data.fintype.basic 
import data.matrix.basic
import .complex_transpose
import linear_algebra.determinant
import linear_algebra.nonsingular_inverse
import tactic 

noncomputable theory 
open_locale classical
open_locale matrix

universes u u'
variables {m n l : Type u} [fintype m] [fintype n] [fintype l]

local notation `Euc` := (n → ℂ)

section unitary 

def matrix.unitary (A : matrix n n ℂ) := 
  A ⬝ (A.complex_transpose) = 1

lemma unit_det_of_unitary {A : matrix n n ℂ} (hu : A.unitary) : is_unit A.det :=
begin 
  have := matrix.det_mul A A.complex_transpose,
  unfold matrix.unitary at hu,
  rw [hu, matrix.det_one] at this,
  exact is_unit_of_mul_eq_one A.det A.complex_transpose.det (eq.symm this),
end 

lemma unit_of_unitary {A : matrix n n ℂ} (hu : A.unitary) : is_unit A :=
  (matrix.is_unit_iff_is_unit_det A).mpr (unit_det_of_unitary hu)

/--------------------------------------------------------------
-- I really need to say that A⁻¹ = A.complex transpose and 
-- A.complex_transpose ⬝ A = 1
--------------------------------------------------------------/

lemma unitary_inv {A : matrix n n ℂ} (hu : A.unitary) : A⁻¹ = A.complex_transpose := 
  sorry

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
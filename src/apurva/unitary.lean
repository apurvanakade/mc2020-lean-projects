import data.complex.basic 
import data.fintype.basic 
import data.fin
import data.matrix.basic
import linear_algebra.basis
import linear_algebra.determinant
import linear_algebra.nonsingular_inverse
import .complex_transpose
import .complex_dot_product
import tactic 

noncomputable theory 
open_locale classical
open_locale matrix

universes u u'
variables {m n l : Type u} [fintype m] [fintype n] [fintype l]
variables {k : ℕ}

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

lemma unitary_inv {A : matrix n n ℂ} (hu : A.unitary) : A⁻¹ = A.complex_transpose := 
begin 
have hA := unit_det_of_unitary hu,
unfold matrix.unitary at hu,
calc 
    A⁻¹ = A⁻¹ ⬝ 1 : by simp only [matrix.mul_one]
    ... = A⁻¹ ⬝ (A ⬝ A.complex_transpose) : by rw hu
    ... = (A⁻¹ ⬝ A) ⬝ A.complex_transpose : by rw matrix.mul_assoc 
    ... = 1 ⬝ A.complex_transpose : by rw A.nonsing_inv_mul hA
    ... = A.complex_transpose : by simp only [matrix.one_mul],
end

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

theorem rows_of_unitary {A : matrix n n ℂ} : 
  A.unitary ↔ 
  ∀ i j : n, 
  (vector.complex_dot_product (A i) (A i) = 1) ∧ 
  i ≠ j → (vector.complex_dot_product (A i) (A j) = 0)
:= sorry

-- how to rewrite this using fin.cons
-- also need a better name
def matrix.extension (A : matrix (fin k) (fin k) ℂ) : matrix (fin (k+1)) (fin (k+1)) ℂ
:= 
λ i j,
match i, j with
| ⟨0, _⟩, ⟨0, _⟩       := 1
| ⟨0, _⟩, _            := 0
| _, ⟨0, _⟩            := 0
| ⟨x+1, hx⟩, ⟨y+1, hy⟩ := A ⟨x, nat.lt_of_succ_lt_succ hx⟩ ⟨y, nat.lt_of_succ_lt_succ hy⟩
end 

lemma extension_unitary_of_unitary {k : ℕ} (A : matrix (fin k) (fin k) ℂ) : 
  A.unitary → A.extension.unitary := 
sorry




end unitary
import data.complex.basic 
import data.fintype.basic 
import data.fin
import data.matrix.basic
import linear_algebra.basis
import linear_algebra.determinant
import linear_algebra.nonsingular_inverse
import .complex_transpose
import .complex_dot_product
import .matrix_extension
import tactic 

noncomputable theory 
open_locale classical
open_locale matrix

universes u u'
variables {m n l : Type u} [fintype m] [fintype n] [fintype l]
variables {k : ℕ}

section unitary 

def matrix.unitary (A : matrix n n ℂ) := 
  A ⬝ (A.complex_transpose) = 1
open matrix

lemma unit_det_of_unitary {A : matrix n n ℂ} (hu : A.unitary) : is_unit A.det :=
begin 
  have := matrix.det_mul A A.complex_transpose,
  unfold matrix.unitary at hu,
  rw [hu, matrix.det_one] at this,
  exact is_unit_of_mul_eq_one A.det A.complex_transpose.det (eq.symm this),
end 

lemma unit_of_unitary {A : matrix n n ℂ} (hu : A.unitary) : is_unit A :=
  (matrix.is_unit_iff_is_unit_det A).mpr (unit_det_of_unitary hu)

lemma unitary_inv {A : matrix n n ℂ} (hu : A.unitary) : A.complex_transpose = A⁻¹ := 
begin
  unfold unitary at hu,
  rw [← mul_one A⁻¹, ← hu], rw [mul_eq_mul, ← matrix.mul_assoc], 
  sorry
end

lemma unit_of_complex_transpose {A : matrix n n ℂ} (hu : A.unitary) : is_unit A.complex_transpose :=
begin
  refine unit_of_unitary _,
  unfold unitary, rw complex_transpose_transpose, rw unitary_inv hu, rw ← mul_eq_mul,
  sorry
end

lemma unitary.has_mul {A B : matrix n n ℂ} (hA : A.unitary) (hB : B.unitary) :
  (A ⬝ B).unitary := 
begin 
  unfold matrix.unitary at *,
  rw [complex_transpose_mul, matrix.mul_assoc, ← matrix.mul_assoc B], simp [hA, hB]
end 

lemma unitary.has_one : (1 : matrix n n ℂ).unitary := by simp [matrix.unitary]
include n
instance unitary_group : group $ subtype $ unitary := 
{ mul := begin
  rintros ⟨A, hA⟩ ⟨B, hB⟩, refine ⟨A ⬝ B, _⟩, exact n, apply_instance, apply unitary.has_mul; assumption,
end,
  mul_assoc := sorry,
  one := ⟨1, unitary.has_one⟩,
  one_mul := sorry,
  mul_one := sorry,
  inv := sorry,
  mul_left_inv := sorry }
-- begin

-- end
-- #check subtype unitary

theorem rows_of_unitary {A : matrix n n ℂ} : 
  A.unitary ↔ 
  ∀ i j : n, 
  (vector.complex_dot_product (A i) (A i) = 1) ∧ 
  i ≠ j → (vector.complex_dot_product (A i) (A j) = 0)
:= sorry

lemma extension_unitary_of_unitary {k : ℕ} (A : matrix (fin k) (fin k) ℂ) (a : ℝ): 
  A.unitary → (A.extension a).unitary := 
sorry

theorem unitary_of_unit_vector [linear_order n] [has_zero n] (v : n → ℂ) : 
  ∥v∥ = 1 → 
  ∃ A : matrix n n ℂ,
  A.unitary ∧ 
  (A 0) = v :=
sorry

end unitary
/-
Define eigenvalues and eigenspaces of matrices and prove new theorems about them. 
-/

import data.matrix.basic
import tactic
import linear_algebra.determinant
import .algebraically_closed
import linear_algebra.nonsingular_inverse
import linear_algebra.char_poly

noncomputable theory
open matrix 
open_locale matrix
open_locale classical

-- comm_semiring = semiring α, comm_monoid α
-- comm_ring = ring + semigroup
-- semiring = add_comm_monoid α, monoid_with_zero α, distrib α 

universes u 

variables {S : Type*} [semiring S]
variables {R : Type*} [ring R]
variables {k : Type*} [field k]
variables {l m n o : Type*} [fintype l] [fintype m] [fintype n] [fintype o]

namespace matrix

def eigenvector (M : matrix n n S) : (n → S) → Prop := 
λ v, ∃ c : S, v ≠ 0 ∧ M.mul_vec v = (c • (1 : matrix n n S)).mul_vec v

def eigenvalue (M : matrix n n S) : S → Prop := 
λ c, ∃ v : n → S, v ≠ 0 ∧ M.mul_vec v = (c • (1 : matrix n n S)).mul_vec v

def eigenvalue_of_eigenvector {M : matrix n n S} {v : n → S} 
(hc : eigenvector M v) : S := 
begin 
  choose c key using hc,
  exact c,
end 

def eigenspace (M : matrix n n S) (c : S) : set (n → S) :=
{v | v = 0 ∨ ((eigenvector M v) ∧ M.mul_vec v = (c • (1 : matrix n n S)).mul_vec v) }

def spectrum (M : matrix n n S) : set S :=
{c | eigenvalue M c}

-- def generalized_eigenspace (M : matrix n n R) (c : R) : set (n → R) :=
-- {v | ∃ k : ℕ, (M - c • 1)^k.mul_vec v = 0}
-- end matrix
end matrix 

instance (M : matrix n n S) (c : S) : add_comm_monoid (matrix.eigenspace M c) := 
{ add := sorry,
  add_assoc := sorry,
  zero := sorry,
  zero_add := sorry,
  add_zero := sorry,
  add_comm := sorry }

instance (M : matrix n n S) (c : S) : semimodule S (matrix.eigenspace M c) := 
{ smul := sorry,
  one_smul := sorry,
  mul_smul := sorry,
  smul_add := sorry,
  smul_zero := sorry,
  add_smul := sorry,
  zero_smul := sorry }

#check mul_vec 

lemma det_zero_iff_sing {M : matrix n n k} :
  M.det = 0 ↔ ∃ v : n → k, v ≠ 0 ∧ M.mul_vec v = 0 := 
begin 
repeat{sorry,},
end

lemma eigenvalue_det {M : matrix n n k} {c : k} :
  (M - c • 1).det = 0 ↔ M.eigenvalue c := 
begin 
  sorry,
end 

#check mul_nonsing_inv

theorem exists_eigenvalue (M : matrix n n ℂ) : (∃ c : ℂ, matrix.eigenvalue M c) :=
begin 
  let k:= ℂ,
  suffices : ∃ c : k, (M - c • 1).det = 0, by sorry,
  set f := char_poly M,
  have hf_deg : 0 < f.degree, by sorry,
  sorry,
end

#check exists_eigenvalue
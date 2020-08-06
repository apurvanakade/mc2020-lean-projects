/-
Define eigenvalues and eigenspaces of matrices and prove new theorems about them. 
-/

import data.matrix.basic
import tactic
import linear_algebra.determinant
import .algebraically_closed
import linear_algebra.char_poly

noncomputable theory
open_locale matrix
open_locale classical

-- comm_semiring = semiring α, comm_monoid α
-- comm_ring = ring + semigroup
-- semiring = add_comm_monoid α, monoid_with_zero α, distrib α 

universes u 

variables {S : Type u} [semiring S]
variables {R : Type u} [ring R]
variables {k : Type u} [field k] [algebraically_closed k] 
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]


namespace matrix
def eigenvalue (M : matrix n n S) : S → Prop := 
λ c, ∃ v : n → S, ∀ i : n, M.mul_vec v i = c * v i

def eigenvector (M : matrix n n S) : (n → S) → Prop := 
λ v, ∃ c : S, ∀ i : n, M.mul_vec v i = c * v i

def eigenvalue_of_eigenvector {M : matrix n n S} {v : n → S} 
(hc : eigenvector M v) : S := 
begin 
  choose c key using hc,
  exact c,
end 

def eigenspace (M : matrix n n S) (c : S) : set (n → S) :=
{v | (eigenvector M v) ∧ (∀ i : n, M.mul_vec v i = c * v i)}

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

-- instance (M : matrix n n R) (c : R) : add_comm_monoid (matrix.generalized_eigenspace M c) := 
-- { add := sorry,
--   add_assoc := sorry,
--   zero := sorry,
--   zero_add := sorry,
--   add_zero := sorry,
--   add_comm := sorry }

-- instance (M : matrix n n R) (c : R) : semimodule R (matrix.generalized_eigenspace M c) := 
-- sorry

lemma eigenvalue_det {M : matrix n n k} {c : k} :
  M.eigenvalue c ↔ (M - c • 1).det = 0 := 
sorry

theorem exists_eigenvalue {M : matrix n n k} : (∃ c : k, M.eigenvalue c) :=
begin 
  suffices : ∃ c : k, (M - c • 1).det = 0, by simpa [eigenvalue_det],
  let f := char_poly M,
  have hf_deg : 0 < f.degree, by sorry,
  have c := _inst_4.exists_root f hf_deg, -- why does this not work?
end 
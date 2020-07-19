/-
Define eigenvalues and eigenspaces of matrices and prove new theorems about them. 
-/

import data.matrix.basic
import tactic
noncomputable theory
open_locale matrix
open_locale classical

-- comm_semiring = semiring α, comm_monoid α
-- comm_ring = ring + semigroup
-- semiring = add_comm_monoid α, monoid_with_zero α, distrib α 

#print add_comm_monoid 
#print comm_monoid

universes u 

variables {S : Type u} [semiring S]
variables {R : Type u} [ring R]
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]

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
sorry

instance (M : matrix n n S) (c : S) : add_comm_monoid (eigenspace M c) := 
{ add := sorry,
  add_assoc := sorry,
  zero := sorry,
  zero_add := sorry,
  add_zero := sorry,
  add_comm := sorry }

instance (M : matrix n n S) (c : S) : semimodule S (eigenspace M c) := 
{ smul := sorry,
  one_smul := sorry,
  mul_smul := sorry,
  smul_add := sorry,
  smul_zero := sorry,
  add_smul := sorry,
  zero_smul := sorry }

def generalized_eigenspace (M : matrix n n R) (c : R) : set (n → R) :=
sorry

instance (M : matrix n n R) (c : R) : add_comm_monoid (generalized_eigenspace M c) := 
{ add := sorry,
  add_assoc := sorry,
  zero := sorry,
  zero_add := sorry,
  add_zero := sorry,
  add_comm := sorry }

instance (M : matrix n n R) (c : R) : semimodule R (generalized_eigenspace M c) := 
sorry

variables {k : Type u} [field k] -- how to say k is algebraically closed?

theorem exists_eigenvalue (M : matrix n n k) : (∃ c : k, eigenvalue M c) :=
sorry

end matrix
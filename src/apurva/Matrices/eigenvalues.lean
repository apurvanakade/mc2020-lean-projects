/-
Define eigenvalues and eigenspaces of matrices and prove new theorems about them. 
-/

import data.matrix.basic
open_locale matrix

-- comm_semiring = semiring α, comm_monoid α
-- comm_ring = ring + semigroup
-- semiring = add_comm_monoid α, monoid_with_zero α, distrib α 

#print add_comm_monoid 
#print comm_monoid

universes u 

variables {R : Type u} [semiring R]
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]

-- def eigenvalue (M : matrix n n R) : R → Prop := 
-- λ c, ∃ v : n → R, ∀ i : n, M.mul_vec v i = c * v i

def eigenvector (M : matrix n n R) : (n → R) → Prop := 
λ v, ∃ c : R, ∀ i : n, M.mul_vec v i = c * v i

def eigenvalue {M : matrix n n R} {v : n → R} 
(hc : eigenvector M v) : R := 
sorry 

def eigenspace (M : matrix n n R) (c : R) : set (n → R) :=
sorry

def spectrum (M : matrix n n R) : set R :=
sorry

def eigenspace.to_semimodule (M : matrix n n R) (c : R) : semimodule R (eigenspace M c) := 
sorry



end matrix
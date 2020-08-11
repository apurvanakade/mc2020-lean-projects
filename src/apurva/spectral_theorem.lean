import .unitary 
import .normal
import .eigenvalues 

noncomputable theory
open_locale matrix
open_locale classical

universes u 

variables {n : Type u} [fintype n] [linear_order n]

lemma upper_triangular_decomposition (M : matrix n n ℂ) : 
  ∃ U L : matrix n n ℂ, U.unitary ∧ L.upper_triangular ∧
  M = U • L • U.complex_transpose
  := 
begin 
  sorry
end 

theorem spectral_theorem {M : matrix n n ℂ} (hn : M.normal) :
  ∃ U : matrix n n ℂ, ∃ D : n → ℂ, 
  U.unitary ∧
  M = U • (matrix.diagonal D) • U.complex_transpose
  := 
begin 
  rcases (upper_triangular_decomposition M) with ⟨U,L,hU,hLu,key⟩,
  have hLn : L.normal, by sorry,
  cases diagonal_of_upper_triangular_normal hLu hLn with D,
  use [U,D],
  split,
  {exact hU},
  {rwa ←h},
end
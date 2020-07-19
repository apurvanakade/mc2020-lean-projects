import .normal_matrix
import linear_algebra.finite_dimensional
import tactic 

noncomputable theory 
open_locale big_operators 

universes u u'
variables {m n : Type u} [fintype m] [fintype n]

local notation `Euc` := (n → ℂ)

def complex_dot_product (v : Euc) (w : Euc) : ℂ := 
∑ i, complex.conj (v i) * w i  

def orthogonal (v : Euc) (w : Euc) : Prop := 
(complex_dot_product v w = 0)  

def orthogonal_complement (v : Euc) : subspace ℂ Euc := 
{ carrier := sorry,
zero_mem' := sorry,
add_mem' := sorry,
smul_mem' := sorry }

def is_orthogonal_subspace (S : set Euc) : subspace ℂ Euc → Prop := 
begin 
  intro W,
  sorry,
end 


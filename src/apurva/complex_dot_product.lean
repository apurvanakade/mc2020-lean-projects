import data.complex.basic 
import data.fintype.basic 
import data.matrix.basic
import linear_algebra.finite_dimensional
import .complex_transpose
import tactic 

noncomputable theory 
open_locale big_operators 

universes u v
variables {n m : Type u} [fintype n] [fintype m]

local notation `Euc` := (n → ℂ)

namespace vector
/-- Complex conjugate of a vector.-/
def conj (M : matrix m n ℂ) : matrix m n ℂ := 
λ i j, complex.conj (M i j)

def complex_dot_product (v : Euc) (w : Euc) : ℂ := 
∑ i, complex.conj (v i) * w i  

def orthogonal (v : Euc) (w : Euc) : Prop := 
(complex_dot_product v w = 0)  

def orthogonal_complement (v : Euc) : subspace ℂ Euc := 
{ carrier := sorry,
  zero_mem' := sorry,
  add_mem' := sorry,
  smul_mem' := sorry }

end vector

namespace subspace 
  -- variables {W : Type u'} [add_comm_group W] [vector_space ℂ W] [finite_dimensional ℂ W]

def is_orthogonal_subspace (S : set Euc) : subspace ℂ Euc → Prop := 
begin 
  intro W,
  sorry,
end 

def orthogonal_complement (S : set Euc) : subspace ℂ Euc := 
Inf {U | ∀ v ∈ S, v ∈ U}

-- CR jstark for apurvnakade: I don't understand what your theorem is supposed to say.
--  Is this version what you were going for?
-- need coercion from subspace to larger space
theorem orthogonal_in_orthogonal_complement 
(S : set Euc) {v w : Euc} (hv : v ∈ S) (hw : w ∈ orthogonal_complement S) : 
  vector.orthogonal v w := 
sorry

end subspace
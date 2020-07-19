import data.complex.basic 
import data.fintype.basic 
import linear_algebra.finite_dimensional
import tactic 

noncomputable theory 
open_locale big_operators 

universes u u'
variables {n : Type u} [fintype n]

local notation `V` := (n → ℂ)

instance hn_fd : finite_dimensional ℂ V := 
begin 
  apply_instance
end 

namespace vector
  /-- Complex conjugate of a vector.-/
  def conj (v : V) : V := 
  λ i, complex.conj (v i)

  def complex_dot_product (v : V) (w : V) : ℂ := 
  ∑ i, complex.conj (v i) * w i

  def orthogonal (v : V) (w : V) : Prop := 
  (complex_dot_product v w = 0)  

  def orthogonal_complement (v : V) : subspace ℂ V := 
  { carrier := sorry,
  zero_mem' := sorry,
  add_mem' := sorry,
  smul_mem' := sorry }

end vector

namespace subspace 
  variables {W : Type u'} [add_comm_group W] [vector_space ℂ W] [finite_dimensional ℂ W]

  def is_orthogonal_subspace (S : set V) : W ≤ V → Prop := 
  begin 
    sorry,
  end 

  def orthogonal_complement (S : set V) : subspace ℂ V := 
  sorry -- infimum of all 

  -- need coercion from subspace to larger space
  theorem orthogonal_in_orthogonal_complement (S : set V) (v : subspace ℂ V) (w : orthogonal_complement S) : 
    vector.orthogonal (v : V) (w : V) := 
  sorry

end subspace
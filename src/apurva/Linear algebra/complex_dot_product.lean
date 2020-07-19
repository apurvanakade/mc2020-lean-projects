import data.complex.basic 
import data.fintype.basic 
import data.matrix.basic
import linear_algebra.finite_dimensional
import tactic 

noncomputable theory 
open_locale big_operators 

universes u u'
variables {n m : Type u} [fintype n] [fintype m]

local notation `Euc` := (n → ℂ)

instance hn_fd : finite_dimensional ℂ Euc := 
begin 
  apply_instance
end 

open matrix
  /-- Complex conjugate of a vector.-/
  def conj (M : matrix m n ℂ) : matrix m n ℂ := 
  λ i j, complex.conj (M i j)

  def complex_transpose (M : matrix m n ℂ) : matrix n m ℂ
  | x y := complex.conj (M y x)

  def complex_dot_product (v : Euc) (w : Euc) : ℂ := 
  ∑ i, complex.conj (v i) * w i  

  def orthogonal (v : Euc) (w : Euc) : Prop := 
  (complex_dot_product v w = 0)  

  def orthogonal_complement (v : Euc) : subspace ℂ Euc := 
  { carrier := sorry,
  zero_mem' := sorry,
  add_mem' := sorry,
  smul_mem' := sorry }

end matrix

namespace subspace 
  -- variables {W : Type u'} [add_comm_group W] [vector_space ℂ W] [finite_dimensional ℂ W]

  def is_orthogonal_subspace (S : set Euc) : subspace ℂ Euc → Prop := 
  begin 
    intro W,
    sorry,
  end 

  def orthogonal_complement (S : set Euc) : subspace ℂ Euc := 
  sorry -- infimum of all 

  -- need coercion from subspace to larger space
  theorem orthogonal_in_orthogonal_complement (S : set Euc) (v : subspace ℂ Euc) (w : orthogonal_complement S) : 
    vector.orthogonal (v : Euc) (w : Euc) := 
  sorry

end subspace
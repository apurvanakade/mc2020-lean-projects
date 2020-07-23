import data.complex.basic 
import data.fintype.basic 
import data.matrix.basic
import linear_algebra.finite_dimensional
import .complex_transpose
import analysis.normed_space.basic
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

@[simp]
lemma complex_dot_product_zero (v : Euc) : complex_dot_product v (0 : Euc) = 0 :=
begin 
  unfold complex_dot_product,
  simp only [pi.zero_apply, finset.sum_const_zero, mul_zero],
end 

@[simp]
lemma zero_complex_dot_product (v : Euc) : complex_dot_product (0 : Euc) v = 0 :=
begin 
  unfold complex_dot_product,
  simp only [zero_mul, pi.zero_apply, ring_hom.map_zero, finset.sum_const_zero],
end 

@[simp]
lemma complex_dot_product_add (v w u : Euc) : 
  complex_dot_product v (w + u) = complex_dot_product v w + complex_dot_product v u := 
sorry

@[simp]
lemma complex_dot_product_sub (v w u : Euc) : 
  complex_dot_product v (w - u) = complex_dot_product v w - complex_dot_product v u := 
sorry

@[simp]
lemma complex_dot_product_smul (v w : Euc) (c : ℂ) : 
  (c * complex_dot_product v w) = complex_dot_product v (c • w) :=
sorry

@[simp]
lemma complex_dot_product_smul' (v w : Euc) (c : ℂ) : 
  (c * complex_dot_product v w) = complex_dot_product (c • v) w :=
sorry


def orthogonal_complement (v : Euc) : subspace ℂ Euc := 
{ carrier := orthogonal v,
  zero_mem' := complex_dot_product_zero v,
  add_mem' := sorry,
  smul_mem' := sorry }

def complex_norm (v : Euc) := complex_dot_product v v

end vector

notation `∥`:1024 v:1 `∥`:1 := v.complex_norm

namespace subspace 
  -- variables {W : Type u'} [add_comm_group W] [vector_space ℂ W] [finite_dimensional ℂ W]

def is_orthogonal (S : set Euc) : subspace ℂ Euc → Prop := 
  λ W, ∀ w ∈ W, ∀ v ∈ S, (vector.complex_dot_product v w = 0)

def orthogonal_complement (S : set Euc) : subspace ℂ Euc := 
Inf {W | is_orthogonal S W}


end subspace
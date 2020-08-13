import data.complex.basic 
import data.fintype.basic 
import data.matrix.basic
import linear_algebra.finite_dimensional
import .complex_transpose
import analysis.normed_space.basic
import tactic 

noncomputable theory 
open_locale big_operators 
open_locale matrix

universes u v
variables {n m : Type u} [fintype n] [fintype m]

local notation `Euc` := (n → ℂ)

namespace vector
/-- Complex conjugate of a vector.-/
@[simp]
def conj (v : Euc) : Euc := 
λ i, complex.conj (v i)

@[simp] 
lemma conj_val (v : Euc) (i : n) : conj v i = complex.conj (v i) := rfl

@[simp] 
lemma smul_conj (x : ℂ) (v : Euc) : 
  conj (x • v) = x.conj • conj(v) :=
by ext; simp

@[simp]
def complex_dot_product (v : Euc) (w : Euc) : ℂ := 
-- ∑ i, complex.conj (v i) * w i 
matrix.dot_product v (conj w)

@[simp]
lemma complex_dot_product_zero {v : Euc} : complex_dot_product v (0 : Euc) = 0 :=
by {ext; simp}

lemma complex_dot_product_symm {v w : Euc} : 
  (complex_dot_product v w) = (complex_dot_product w v).conj :=
sorry

@[simp]
lemma zero_complex_dot_product {v : Euc} : complex_dot_product (0 : Euc) v = 0 :=
by {ext;simp}

@[simp]
lemma add_complex_dot_product {v w u : Euc} : 
  complex_dot_product (v + w) u = complex_dot_product v u + complex_dot_product w u := 
by {ext;simp}

@[simp]
lemma complex_dot_product_add {v w u : Euc} : 
  complex_dot_product v (w + u) = complex_dot_product v w + complex_dot_product v u := 
by {rw [complex_dot_product_symm, @complex_dot_product_symm _ _ v w, @complex_dot_product_symm _ _ v u], 
  simp only [conj, ring_hom.map_add, eq_self_iff_true, add_complex_dot_product]}

@[simp]
lemma complex_dot_product_sub {v w u : Euc} : 
  complex_dot_product (v - w) u = complex_dot_product v u - complex_dot_product w u := 
begin 
suffices : complex_dot_product v u = complex_dot_product (v - w) u +  complex_dot_product w u,
by exact eq_sub_of_add_eq (eq.symm this),
set u' := v - w with hu,
have : v = u' + w, by {exact eq_add_of_sub_eq rfl},
rw this, apply add_complex_dot_product,
end 

@[simp] 
lemma diagonal_complex_dot_product [decidable_eq n] (v w : Euc) (i : n) :
  complex_dot_product (matrix.diagonal v i) w = v i * w i :=
have ∀ j ≠ i, matrix.diagonal v i j * w j = 0 := λ j hij, 
  by simp [matrix.diagonal_val_ne' hij],
  by convert finset.sum_eq_single i (λ j _, this j) _; sorry

@[simp] 
lemma complex_dot_product_diagonal [decidable_eq n] (v w : Euc) (i : n) :
  complex_dot_product v (matrix.diagonal w i) = v i * w i :=
have ∀ j ≠ i, v j * matrix.diagonal w i j = 0 := λ j hij, by simp [matrix.diagonal_val_ne' hij],
by convert finset.sum_eq_single i (λ j _, this j) _; sorry

@[simp] lemma complex_dot_product_diagonal' [decidable_eq n] (v w : Euc) (i : n) :
  complex_dot_product v (λ j, matrix.diagonal w j i) = v i * w i :=
have ∀ j ≠ i, v j * matrix.diagonal w j i = 0 := λ j hij, by simp [matrix.diagonal_val_ne hij],
by convert finset.sum_eq_single i (λ j _, this j) _; sorry

@[simp] lemma neg_complex_dot_product (v w : Euc) : 
  complex_dot_product (-v) w = - complex_dot_product v w :=
by simp [matrix.dot_product]

@[simp] lemma complex_dot_product_neg (v w : Euc) : complex_dot_product v (-w) = - complex_dot_product v w :=
by simp only [matrix.dot_product, conj, pi.neg_apply, mul_neg_eq_neg_mul_symm, ring_hom.map_neg, finset.sum_neg_distrib,
 complex_dot_product]

@[simp] lemma smul_complex_dot_product (x : ℂ) (v w : Euc) :
  complex_dot_product (x • v) w = x * complex_dot_product v w :=
by simp only [complex_dot_product, matrix.smul_dot_product]

@[simp] lemma complex_dot_product_smul (x : ℂ) (v w : Euc) :
  complex_dot_product v (x • w) = x.conj * complex_dot_product v w :=
by simp only [complex_dot_product, smul_conj, matrix.dot_product_smul]

@[simp]
def orthogonal (v : Euc) (w : Euc) : Prop := 
(complex_dot_product v w = 0) 

def complex_norm (v : Euc) := complex_dot_product v v

end vector

section subspace 
def is_orthogonal (S : set Euc) : subspace ℂ Euc → Prop := 
  λ W, ∀ w ∈ W, ∀ v ∈ S, (vector.complex_dot_product v w = 0)

def orthogonal_complement (S : set Euc) : subspace ℂ Euc := 
Inf {W | is_orthogonal S W}

end subspace
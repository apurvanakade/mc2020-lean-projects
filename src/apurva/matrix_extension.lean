import data.complex.basic 
import data.fintype.basic 
import data.fin
import data.matrix.basic
import linear_algebra.basis
import linear_algebra.determinant
import linear_algebra.nonsingular_inverse
import .complex_transpose
import tactic 


noncomputable theory 
open_locale classical
open_locale matrix

universes u u'
variables {m n l : Type u} [fintype m] [fintype n] [fintype l]
variables {k : ℕ}

-- how to rewrite this using fin.cons
-- also need a better name
def matrix.extension (A : matrix (fin k) (fin k) ℂ) (a : ℂ) : 
  matrix (fin (k+1)) (fin (k+1)) ℂ
:= 
λ i j,
match i, j with
| ⟨0, _⟩, ⟨0, _⟩       := a
| ⟨0, _⟩, _            := 0
| _, ⟨0, _⟩            := 0
| ⟨x+1, hx⟩, ⟨y+1, hy⟩ := A ⟨x, nat.lt_of_succ_lt_succ hx⟩ ⟨y, nat.lt_of_succ_lt_succ hy⟩
end 

-- set_option pp.notation false
lemma matrix.extension_mul (A B : matrix (fin k) (fin k) ℂ) (a b : ℂ) : 
  (A.extension a)⬝ (B.extension b) = (A ⬝ B).extension (a * b):=
begin 
rw ←matrix.ext_iff,
intros i j,
unfold has_mul.mul, 
sorry,
end

lemma matrix.extension_conj (A : matrix (fin k) (fin k) ℂ) (a : ℂ): 
  (A.extension a).conj = A.conj.extension a.conj := sorry 


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
def matrix.extension (A : matrix (fin k) (fin k) ℂ) : matrix (fin (k+1)) (fin (k+1)) ℂ
:= 
λ i j,
match i, j with
| ⟨0, _⟩, ⟨0, _⟩       := 1
| ⟨0, _⟩, _            := 0
| _, ⟨0, _⟩            := 0
| ⟨x+1, hx⟩, ⟨y+1, hy⟩ := A ⟨x, nat.lt_of_succ_lt_succ hx⟩ ⟨y, nat.lt_of_succ_lt_succ hy⟩
end 

lemma matrix.extension_mul (A : matrix (fin k) (fin k) ℂ)
(B : matrix (fin k) (fin k) ℂ) : 
(A ⬝ B).extension = A.extension ⬝ B.extension :=
sorry 

lemma matrix.extension_conj (A : matrix (fin k) (fin k) ℂ) : 
  A.extension.conj = A.conj.extension := sorry 


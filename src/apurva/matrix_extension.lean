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
variables {n : ℕ}
variables {S : Type u} [semiring S]

-- need a better name
def matrix.extension (A : matrix (fin n) (fin n) S) (a : S) : 
  matrix (fin (n+1)) (fin (n+1)) S
:= 
λ i j,
match i, j with
| ⟨0, _⟩, ⟨0, _⟩       := a
| ⟨0, _⟩, _            := 0
| _, ⟨0, _⟩            := 0
| ⟨x+1, hx⟩, ⟨y+1, hy⟩ := A ⟨x, nat.lt_of_succ_lt_succ hx⟩ ⟨y, nat.lt_of_succ_lt_succ hy⟩
end 

def vector.extension (v : (fin n) → S) (a : S) : 
  fin (n+1) → S
:= 
λ i,
match i with
| ⟨0, _⟩      := a
| ⟨x+1, hx⟩   := v ⟨x, nat.lt_of_succ_lt_succ hx⟩
end 


-- set_option pp.notation false
lemma matrix.extension_mul (A B : matrix (fin n) (fin n) S) (a b : S) : 
  (A.extension a) • (B.extension b) = (A • B).extension (a * b):=
begin 
ext,
cases i, cases i_val,
cases j, cases j_val,
sorry,
repeat{sorry,}
end

lemma matrix.extension_conj (A : matrix (fin n) (fin n) ℂ) (a : ℂ) : 
  (A.extension a).conj = A.conj.extension a.conj :=
begin 
sorry,
end


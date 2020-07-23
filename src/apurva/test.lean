import data.fintype.basic 
import data.matrix.basic

open_locale matrix

def matrix_extension {k : ℕ} (A : matrix (fin k) (fin k) ℕ) : matrix (fin (k+1)) (fin (k+1)) ℕ
:=
λ i j,
match i, j with
| ⟨0, _⟩, ⟨0, _⟩       := 1
| ⟨0, _⟩, _            := 0
| _, ⟨0, _⟩            := 0
| ⟨x+1, hx⟩, ⟨y+1, hy⟩ := A ⟨x, nat.lt_of_succ_lt_succ hx⟩ ⟨y, nat.lt_of_succ_lt_succ hy⟩
end
import data.complex.basic 
import data.fintype.basic 
import data.matrix.basic
import linear_algebra.nonsingular_inverse
import tactic 

noncomputable theory 
open_locale classical

universes u u'
variables {m n : Type u} [fintype m] [fintype n]

local notation `Euc` := (n → ℂ)

/-- Complex conjugate of a vector.-/
def conj (M : matrix m n ℂ) : matrix m n ℂ := 
λ i j, complex.conj (M i j)

def complex_transpose (M : matrix m n ℂ) : matrix n m ℂ
| x y := complex.conj (M y x)

class hermitian (A : matrix n n ℂ) := 
(is_hermitian : A = complex_transpose A)

class normal (A : matrix n n ℂ) := 
(is_normal : A • complex_transpose A = complex_transpose A • A)

instance normal_of_hermitian {A : matrix n n ℂ} [hh : hermitian A] : normal A := 
{is_normal := by rw ←hh.is_hermitian}

class unitary (A : matrix n n ℂ) := 
(is_unitary : A • (complex_transpose A) = 1)

lemma is_unit_det_of_unitary (A : matrix n n ℂ) [hu : unitary A] : is_unit A.det :=
begin 
  sorry,
end 



lemma is_unit_of_unitary (A : matrix n n ℂ) [hu : unitary A] : is_unit A :=
  (matrix.is_unit_iff_is_unit_det A).mpr (is_unit_det_of_unitary A)

instance normal_of_unitary {A : matrix n n ℂ} [hu : unitary A] : normal A := 
{is_normal := 
  begin 
    have := hu.is_unitary, clear hu,
    rw this,
    symmetry,
    sorry,
  end}


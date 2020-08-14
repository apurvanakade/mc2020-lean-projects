import .unitary 
import .normal
import .eigenvalues 
import .algebraically_closed

noncomputable theory
open_locale matrix
open_locale classical

lemma spectral_theorem {n : ℕ} (M : matrix (fin n) (fin n) ℂ) (hn : M.normal) : 
  ∃ U : matrix (fin n) (fin n) ℂ, 
  ∃ D : (fin n) → ℂ,
  U.unitary ∧
    M = U • (matrix.diagonal D) • U.complex_transpose := 
begin 
induction n with n ind, by sorry, -- what is (fin 0)?
rcases exists_eigenvalue M with ⟨c, v, hne0, heigen⟩,
let v' := (vector.complex_norm v)⁻¹ • v,
have : vector.complex_norm v' = 1, by sorry,
rcases unitary_of_unit_vector v' this with ⟨U, hU, hv'⟩,
have hext : ∃ B (c : ℝ), U.conj • M • U = matrix.extension B c ∧ B.normal, by sorry,
rcases hext with ⟨ B, c, key_ext, hB ⟩,
specialize ind B hB,
rcases ind with ⟨U', D', hU', key_B ⟩,
use [U • (U'.extension 1), vector.extension D' c],
split,
sorry,
sorry
end 

-- theorem spectral_theorem {M : matrix n n ℂ} (hn : M.normal) :
--   ∃ U : matrix n n ℂ, ∃ D : n → ℂ, 
--   U.unitary ∧
--   M = U • (matrix.diagonal D) • U.complex_transpose
--   := 
-- begin 
--   rcases (upper_triangular_decomposition M) with ⟨U,L,hU,hLu,key⟩,
--   have hLn : L.normal, by sorry,
--   cases diagonal_of_upper_triangular_normal hLu hLn with D,
--   use [U,D],
--   split,
--   {exact hU},
--   {rwa ←h},
-- end
import tactic 
import algebra.field 
import analysis.complex.polynomial
import data.multiset.basic

noncomputable theory
open_locale classical

open complex polynomial

universes u 
variables {k : Type u}  [field k]

class algebraically_closed (k : Type u) extends field k :=
(exists_root (f : polynomial k) (hf : 0 < degree f) : ∃ z : k, is_root f z)

instance : algebraically_closed ℂ := 
sorry 

-- need a better name
lemma linear_factor_poly [algebraically_closed k] {f : polynomial ℂ} (hf : 0 < degree f) : 
  ∃ S : multiset (polynomial ℂ), 
  (S.card : with_bot ℕ) = degree f ∧ 
  ∀ (g : polynomial ℂ), g ∈ S → degree g = 1 ∧ 
  f = S.prod :=
sorry --proof by induction on degree 
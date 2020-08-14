import tactic 
import algebra.field 
import analysis.complex.polynomial
import data.multiset.basic
import field_theory.splitting_field

noncomputable theory
open_locale classical

open complex polynomial

universes u 
variables {k : Type u}  [field k]

class algebraically_closed (k : Type u) extends field k :=
(exists_root (f : polynomial k) (hf : 0 < degree f) : ∃ z : k, is_root f z)


-- need a better name
lemma linear_factor_poly [algebraically_closed k] {f : polynomial ℂ} (hge0 : 0 < f.degree) : 
  splits (ring_hom.id ℂ) f :=
begin 
sorry,
end 

instance : algebraically_closed ℂ := 
sorry

#check splits
#check ring_hom.id ℂ

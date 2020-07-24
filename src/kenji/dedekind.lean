import ring_theory.fractional_ideal
import ring_theory.discrete_valuation_ring
universes u v 

variables (R : Type u) [comm_ring R] {A : Type v} [comm_ring A]
variables (K : Type u) [field K] (R' : Type u) [integral_domain R']
variables [algebra R A]

open function
open_locale big_operators

structure is_integrally_closed_in : Prop :=
(inj : injective (algebra_map R A))
(closed : ∀ (a : A), is_integral R a → ∃ r : R, algebra_map R A r = a)

def is_integrally_closed_domain : Prop := ∀ {r s : R}, s ≠ 0 → (∃ (n : ℕ) (f : ℕ → R) (hf : f 0 = 1),
    ∑ ij in finset.nat.antidiagonal n, f ij.1 * r ^ ij.2 * s ^ ij.1 = 0) → s ∣ r
/-
Def 1: integral domain, noetherian, integrally closed, nonzero prime ideals are maximal
-/
class dedekind_id [integral_domain R] : Prop := 
    (noetherian : is_noetherian_ring R)
    (int_closed : is_integrally_closed_domain R)
    (max_nonzero_primes : ∀ P : ideal R, P ≠ ⊥  → P.is_prime → P.is_maximal)
/-
Def 2: noetherian ring,
localization at each nonzero prime ideals is a DVR.

Something is a discrete valuation ring if
it is an integral domain and is a PIR and has one non-zero maximal ideal.
-/
-- class discrete_valuation_ring [comm_ring R] : Prop :=
--     (int_domain : is_integral_domain(R))
--     (unique_nonzero_prime : ∃ Q : ideal R,
--     Q ≠ ⊥ → Q.is_prime →  (∀ P : ideal R, P.is_prime → P = ⊥ ∨ P = Q)
--     )
--     (is_pir : is_principal_ideal_ring(R))
theorem local_id_is_id [integral_domain R'] (S : submonoid R') (zero_non_mem : ((0 : R') ∉  S)) {f : localization_map(S)(localization S)} : is_integral_domain (localization S) :=
begin
  split,
    {--nontrivial localization (pair ne)
      use f.to_fun(1),
      use f.to_fun(0),
      intro one_eq_zero,
      have h2 := (localization_map.eq_iff_exists(f)).1 one_eq_zero,
      cases h2 with c h2,
      rw [zero_mul, one_mul] at h2,
      rw ← h2 at zero_non_mem,
      exact zero_non_mem(c.property),
    },
    {exact mul_comm,},
    {--bulk
      intros x y mul_eq_zero,
      cases f.surj' x with a akey,
      cases f.surj' y with b bkey,
      have h1 : x * (f.to_fun( a.snd)) * y * (f.to_fun(b.snd))= 0,
      { rw [mul_assoc x, ← mul_comm y, ← mul_assoc, mul_eq_zero], simp },
      rw [akey, mul_assoc, bkey, ← f.map_mul', ← f.map_zero'] at h1,
      rw f.eq_iff_exists' at h1,
      cases h1 with c h1, 
      rw [zero_mul, mul_comm] at h1,
      have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1,
      cases h2 with c_eq_zero h2,
      {exfalso,
        rw ← c_eq_zero at zero_non_mem,
        exact zero_non_mem(c.property),
      },
      replace h2 := eq_zero_or_eq_zero_of_mul_eq_zero h2,
      cases h2 with a_eq_zero b_eq_zero,
      { left, rw a_eq_zero at akey,
        exact localization_map.eq_zero_of_fst_eq_zero f akey rfl },
      { right, rw b_eq_zero at bkey,
        exact localization_map.eq_zero_of_fst_eq_zero f bkey rfl },
    },
end

theorem local_at_prime_of_id_is_id (P : ideal R')(hp_prime : P.is_prime) : integral_domain (localization.at_prime(P)) :=
begin
  have zero_non_mem : (0 : R') ∉ P.prime_compl,
  {have := ideal.zero_mem P, simpa,},
  have h1 := local_id_is_id(R')(P.prime_compl)(zero_non_mem),
  exact is_integral_domain.to_integral_domain (localization.at_prime P) h1,
  exact localization.of (ideal.prime_compl P),
end


-- I think making the following instance is *not* the right way forward.
-- instance (P : ideal R) (hp1 : P ≠ ⊥) (hp2 : P.is_prime) : discrete_valuation_ring (localization.at_prime P) := 

class dedekind_dvr [integral_domain R'] : Prop :=
(noetherian : is_noetherian_ring R')
(local_dvr_nonzero_prime : ∀ P : ideal R', P ≠ ⊥ → P.is_prime → 
  @discrete_valuation_ring
    (localization.at_prime P)
    begin
      apply local_at_prime_of_id_is_id,
    end )
/-
Def 3: every nonzero fractional ideal is invertible.

Fractional ideal: I = {r | rI ⊆ R}
It is invertible if there exists a fractional ideal J
such that IJ=R.
-/

class dedekind_inv [integral_domain R'] (f : localization_map(non_zero_divisors R')(localization (non_zero_divisors R'))): Prop :=
    (inv_ideals : ∀ I : ring.fractional_ideal f,
    (∃ t : I, t ≠ 0) →  (∃ J : ring.fractional_ideal f, I*J = 1))
/-
The localization of an integral domain is another integral domain.
-/



/-
TODO: Abstract a lot of the nontrivial proofs.
-/
#print discrete_valuation_ring
instance dedekind_id_imp_dedekind_dvr [dedekind_id R'] : dedekind_dvr R'  :=
begin
  --let f : ideal R' → _ := localization_map.at_prime( localization.at_prime(_)),
  refine {noetherian := dedekind_id.noetherian, local_dvr_nonzero_prime := _},
  -- the previous line is easily found with `suggest`
  intros P hp_nonzero hp_prime,
  letI := hp_prime,
  --this is very hacky, might be able to use above let f : ideal R' → _ expression
  have f := localization.of (ideal.prime_compl P),
  letI := local_at_prime_of_id_is_id(R')(P)(hp_prime),
  refine (discrete_valuation_ring.iff_PID_with_one_nonzero_prime (localization.at_prime P)).mpr _,
  split,
  tactic.swap,
  

  repeat {sorry},
end

instance dedekind_dvr_imp_dedekind_inv [dedekind_dvr R'] (f : fraction_map(R')(localization (non_zero_divisors R')) ): dedekind_inv R' f :=
begin
    sorry,
end

instance dedekind_inv_imp_dedekind_id (f : fraction_map(R')(localization (non_zero_divisors R'))) [dedekind_inv R' f] : dedekind_id R' :=
begin
  sorry,
end

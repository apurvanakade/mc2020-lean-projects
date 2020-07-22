import ring_theory.noetherian
import ring_theory.localization
import ring_theory.ideals
import ring_theory.fractional_ideal
universe u
universe v

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
class discrete_valuation_ring [comm_ring R] : Prop :=
    (int_domain : is_integral_domain(R))
    (is_pir : is_principal_ideal_ring(R))
    (unique_nonzero_prime : ∃ Q : ideal R,
    Q ≠ ⊥ → Q.is_prime →  (∀ P : ideal R, P.is_prime → P = ⊥ ∨ P = Q)
    )

class dedekind_dvr [integral_domain R] : Prop :=
    (noetherian : is_noetherian_ring R)
    (local_dvr_nonzero_prime : ∀ P : ideal R,
    P ≠ ⊥ → P.is_prime → discrete_valuation_ring(localization.at_prime(P)))
/-
Def 3: every nonzero fractional ideal is invertible.

Fractional ideal: I = {r | rI ⊆ R}
It is invertible if there exists a fractional ideal J
such that IJ=R.

Might have to scrap this definition, not able to instatiate something of this type.
-/
class dedekind_inv [integral_domain R'] [comm_ring K] (f : localization_map(non_zero_divisors R')(K)): Prop :=
    (inv_ideals : ∀ I : ring.fractional_ideal f,
    (∃ t : I, t ≠ 0) →  (∃ J : ring.fractional_ideal f, I*J = 1))
/-
The localization of an integral domain is another integral domain.
Needs a few more hypothesis: R' is nontrivial, S does not contain 0, etc.
-/
/- linter hates me
instance local_id_is_id [integral_domain R'] (S : submonoid R') (rule_4 : ((0 : R') ∉  S)) {f : localization_map(S)(localization S)} : integral_domain (localization S) :=
begin
  split,
    {exact mul_comm,},
    {--nontrivial localization (pair ne) (likely more hypothesis needed)
      sorry,
    },
    { --bulk, x * y = 0 → x = 0 ∨ y = 0
      intros x y mul_eq_zero,
      cases f.surj'(x) with a akey,
      cases f.surj'(y) with b bkey,
      have h1 : x * (f.to_fun( a.snd)) * y * (f.to_fun(b.snd))= 0,
        {rw [mul_assoc(x), ← mul_comm(y), ← mul_assoc, mul_eq_zero,zero_mul,zero_mul],},
      rw [akey, mul_assoc,bkey, ← f.map_mul', ← f.map_zero'] at h1,
      rw [f.eq_iff_exists'(a.fst * b.fst)(0)] at h1,
      cases h1 with c h1,
      rw [zero_mul,mul_comm] at h1,
      have h2 := eq_zero_or_eq_zero_of_mul_eq_zero(h1),
      cases h2 with c_eq_zero h2,
      {exfalso, --c cannot both be zero and in S.
        
        
        sorry,
      },
      have h2 := eq_zero_or_eq_zero_of_mul_eq_zero(h2),
      have blah : ((0 : R') = 0), ring,
      cases h2 with a_eq_zero b_eq_zero,
      {left,
        rw a_eq_zero at akey,
        exact localization_map.eq_zero_of_fst_eq_zero(f)(akey)(blah), --eq_zero_blah has terrible documentation
      },
      {right,
        rw b_eq_zero at bkey,
        exact localization_map.eq_zero_of_fst_eq_zero(f)(bkey)(blah),
      },
    },
end
-/



instance dedekind_id_imp_dedekind_dvr [dedekind_id R'] : dedekind_dvr R'  :=
begin
  --let f : ideal R' → _ := localization_map.at_prime( localization.at_prime(_)),
  split,
  {exact dedekind_id.noetherian,},
  {intros P hp_nonzero hp_prime,
    split,
    {--localization of int domain gives int domain. 
    --abstracting this proof would be good.
      letI := hp_prime,
      --this is very hacky, might be able to use above let f : ideal R' → _ expression
      have f : localization_map.at_prime(localization.at_prime P)(P), sorry,
      split,
      {exact exists_pair_ne (localization.at_prime P),},
      {exact mul_comm,},
      intros x y mul_eq_zero,
      cases f.surj'(x) with a akey,
      cases f.surj'(y) with b bkey,
      have h1 : x * (f.to_fun( a.snd)) * y * (f.to_fun(b.snd))= 0,
        {rw [mul_assoc(x), ← mul_comm(y), ← mul_assoc, mul_eq_zero,zero_mul,zero_mul],},
      rw [akey, mul_assoc,bkey, ← f.map_mul', ← f.map_zero'] at h1,
      rw [f.eq_iff_exists'(a.fst * b.fst)(0)] at h1,
      -- c is not in the complement of the primes
      cases h1 with c h1,
      rw [zero_mul,mul_comm] at h1,
      have h2 := eq_zero_or_eq_zero_of_mul_eq_zero(h1),
      cases h2 with c_eq_zero h2,
      {exfalso, --c cannot both be zero and in the complement of P.
        clear h1 akey a bkey b mul_eq_zero x y f,
        have h4 : (0 : R') ∉  P.prime_compl, exact not_not_intro(ideal.zero_mem P),
        contrapose! h4,
        rw ← c_eq_zero, apply c.property,
      },
      have h2 := eq_zero_or_eq_zero_of_mul_eq_zero(h2),
      have blah : ((0 : R') = 0), ring,
      cases h2 with a_eq_zero b_eq_zero,
      {left,
        rw a_eq_zero at akey,
        exact localization_map.eq_zero_of_fst_eq_zero(f)(akey)(blah), --eq_zero_blah has terrible documentation
      },
      {right,
        rw b_eq_zero at bkey,
        exact localization_map.eq_zero_of_fst_eq_zero(f)(bkey)(blah),
      },
    },
    { --is_pir
      split,
      intro S,
      sorry,
    },
    {--unique ideal
      sorry,
    },
  },
end
/-
instance dedekind_dvr_imp_dedekind_inv [dedekind_dvr R'] [field K]: dedekind_inv R' :=
begin
    sorry,
end

#check R'
#check dedekind_inv
instance dedekind_inv_imp_dedekind_id [field K] [dedekind_inv R' K] : dedekind_id R' :=
begin
  sorry,
end
-/

#check localization_map.eq_zero_of_fst_eq_zero
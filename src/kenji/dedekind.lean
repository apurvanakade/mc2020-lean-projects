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
-/
class dedekind_inv [integral_domain R'] [comm_ring K] {f : localization_map(non_zero_divisors R')(K)}: Prop :=
    (inv_ideals : ∀ I : ring.fractional_ideal f,
    (∃ t : I, t ≠ 0) →  (∃ J : ring.fractional_ideal f, I*J = 1))

instance dedekind_id_imp_dedekind_dvr [dedekind_id R'] [comm_ring K] : dedekind_dvr R'  :=
begin
  --let f : ideal R' → _ := localization_map.at_prime(K),
  split,
  {exact dedekind_id.noetherian,},
  {intros P hp_nonzero hp_prime,
    split,
    {--localizations of integral domains gives an integral domain
      --let f := localization_map.at_prime(K)(P)(hp_prime),
      sorry,
    },
    { --is_pir
      
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
#check localization_map.at_prime
namespace testing
universe w
variables (S: Type w) [integral_domain S] (Q : ideal S) (hq : Q.is_prime) (hq_nonzero : Q ≠ ⊥ ) (L : Type w) [comm_ring L]
variables f : localization_map.at_prime(L)(Q)

#check f.to_map(-10)


end testing
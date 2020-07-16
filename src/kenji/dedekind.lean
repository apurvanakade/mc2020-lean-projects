import ring_theory.noetherian
import ring_theory.localization
import ring_theory.ideals
import ring_theory.fractional_ideal
universe u
universe v

variables (R : Type u) {A : Type v}
variables [comm_ring R] [comm_ring A]
variables [algebra R A]

open function
open_locale big_operators

structure is_integrally_closed_in : Prop :=
(inj : injective (algebra_map R A))
(closed : ∀ (a : A), is_integral R a → ∃ r : R, algebra_map R A r = a)

def is_integrally_closed_domain : Prop := ∀ {r s : R}, s ≠ 0 → (∃ (n : ℕ) (f : ℕ → R) (hf : f 0 = 1),
    ∑ ij in finset.nat.antidiagonal n, f ij.1 * r ^ ij.2 * s ^ ij.1 = 0) → s ∣ r

structure Dedekind_domain_id [integral_domain R] : Prop := 
    (noetherian : is_noetherian_ring R)
    (int_closed : is_integrally_closed_domain R)
    (max_prime_ideals : ∀ I : ideal R, (∃ t : I, t ≠ 0) → I.is_prime → I.is_maximal)
#check Dedekind_domain_id

variables [integral_domain R]
variables S : Dedekind_domain_id R
#check S
/-
A dedekind domain is a noetherian ring such that
the localization at each of the maximal prime ideals
(read non-zero prime ideals) is a DVR.

Something is a discrete valuation ring if
it is an integral domain and is a PIR.
-/

class Dedekind_domain_dvr [comm_ring R] : Prop :=
    (noetherian : is_noetherian_ring R)
    (local_pir : ∀ P : ideal R, P.is_prime) --this is wrong, needs to include a statement about the localization

/-
A dedekind domain is a ring such that every
nonzero fractional zero is invertible.

Fractional ideal: I = {r | rI ⊆ R}
It is invertible if there exists a fractional ideal J
such that IJ=R.
-/
class Dedekind_domain_inv [comm_ring R] : Prop :=
    --(inv_ideals : ∀ I : ) --??? fractional ideals seem annoying.
    (yes : tt)
#print has_div
--instance Dedekind_domain_id_imp_Dedekind_domain_dvr (X : type) [Dedekind_domain_id X] : Dedekind_domain_dvr X
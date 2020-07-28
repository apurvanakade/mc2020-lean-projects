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

/-!
Any nontrivial localization of an integral domain results in an integral domain.
-/
theorem local_id_is_id [integral_domain R'] (S : submonoid R') (zero_non_mem : ((0 : R') ∉  S)) {f : localization_map S (localization S)} : 
  is_integral_domain (localization S) :=
begin
  split,
    {--nontrivial localization (pair ne)
      use f.to_fun 1,
      use f.to_fun 0,
      intro one_eq_zero, 
      have h2 := (localization_map.eq_iff_exists f).1 one_eq_zero,
      cases h2 with c h2,
      rw [zero_mul, one_mul] at h2,
      rw ← h2 at zero_non_mem,
      exact zero_non_mem c.property },
    { exact mul_comm },
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
      { exfalso,
        rw ← c_eq_zero at zero_non_mem,
        exact zero_non_mem c.property },
      replace h2 := eq_zero_or_eq_zero_of_mul_eq_zero h2,
      cases h2 with a_eq_zero b_eq_zero,
      { left, rw a_eq_zero at akey,
        exact localization_map.eq_zero_of_fst_eq_zero f akey rfl },
      { right, rw b_eq_zero at bkey,
        exact localization_map.eq_zero_of_fst_eq_zero f bkey rfl },
    },
end

/-!
The localization of an integral domain at a prime ideal is an integral domain.
-/
lemma local_at_prime_of_id_is_id (P : ideal R') (hp_prime : P.is_prime) : 
  integral_domain (localization.at_prime P) :=
begin
  have zero_non_mem : (0 : R') ∉ P.prime_compl,
  { have := ideal.zero_mem P, simpa },
  have h1 := local_id_is_id R' P.prime_compl zero_non_mem,
  exact is_integral_domain.to_integral_domain (localization.at_prime P) h1,
  exact localization.of (ideal.prime_compl P),
end

/-
Chopping block: 
-- class discrete_valuation_ring [comm_ring R] : Prop :=
--     (int_domain : is_integral_domain(R))
--     (unique_nonzero_prime : ∃ Q : ideal R,
--     Q ≠ ⊥ → Q.is_prime →  (∀ P : ideal R, P.is_prime → P = ⊥ ∨ P = Q)
--     )
--     (is_pir : is_principal_ideal_ring(R))
-/


/-!
Def 1: integral domain, noetherian, integrally closed, nonzero prime ideals are maximal
-/
class dedekind_id [integral_domain R] : Prop := 
    (noetherian : is_noetherian_ring R)
    (int_closed : is_integrally_closed_domain R)
    (max_nonzero_primes : ∀ P ≠ (⊥ : ideal R), P.is_prime → P.is_maximal)
/-
Def 2: noetherian ring,
localization at each nonzero prime ideals is a DVR.

Something is a discrete valuation ring if
it is an integral domain and is a PIR and has one non-zero maximal ideal.
-/

class dedekind_dvr [integral_domain R'] : Prop :=
(noetherian : is_noetherian_ring R')
(local_dvr_nonzero_prime : ∀ P ≠ (⊥ : ideal R'), P.is_prime → 
  @discrete_valuation_ring (localization.at_prime P) (by apply local_at_prime_of_id_is_id))

/-
Def 3: every nonzero fractional ideal is invertible.

Fractional ideal: I = {r | rI ⊆ R}
It is invertible if there exists a fractional ideal J
such that IJ=R.
-/

class dedekind_inv [integral_domain R'] (f : localization_map (non_zero_divisors R') $ localization (non_zero_divisors R')) : Prop :=
  (inv_ideals : ∀ I : ring.fractional_ideal f, (∃ t : I, t ≠ 0) → (∃ J : ring.fractional_ideal f, I * J = 1))


lemma dedekind_id_imp_dedekind_dvr [dedekind_id R'] : dedekind_dvr R' :=
begin
  refine {noetherian := dedekind_id.noetherian, local_dvr_nonzero_prime := _},
  intros P hp_nonzero hp_prime, letI := hp_prime,
  have f := localization.of (ideal.prime_compl P),
  letI := local_at_prime_of_id_is_id R' P hp_prime,
  rw discrete_valuation_ring.iff_PID_with_one_nonzero_prime (localization.at_prime P),
  split, swap,
  {
    have p' := local_ring.maximal_ideal (localization.at_prime P),
    have hp' := local_ring.maximal_ideal.is_maximal (localization.at_prime P),
    split,
    refine ⟨_, _⟩,
    
    repeat {sorry},
  },

  repeat {sorry},
end


-- CR jstark for kenji: You don't want both of these to be instances, since that creates a loop in typeclass inference.
-- I'd guess both of these just want to be lemmas
lemma dedekind_dvr_imp_dedekind_inv [dedekind_dvr R'] (f : fraction_map R' $ localization (non_zero_divisors R')) : 
  dedekind_inv R' f :=
begin
    sorry,
end

lemma dedekind_inv_imp_dedekind_id (f : fraction_map R' $ localization (non_zero_divisors R')) [dedekind_inv R' f] : 
  dedekind_id R' :=
begin
  sorry,
end

lemma dedekind_id_imp_dedekind_inv [dedekind_id R'] (f : fraction_map R' $ localization (non_zero_divisors R')) : dedekind_inv R' f :=
by {letI := dedekind_id_imp_dedekind_dvr R', exact dedekind_dvr_imp_dedekind_inv R' f,}

lemma dedekind_inv_imp_dedekind_dvr (f : fraction_map R' $ localization (non_zero_divisors R')) [dedekind_inv R' f] : dedekind_dvr R' :=
by {letI := dedekind_inv_imp_dedekind_id R', exact dedekind_id_imp_dedekind_dvr R',}

lemma dedekind_dvr_imp_dedekind_id (f : fraction_map R' $ localization (non_zero_divisors R')) [dedekind_dvr R'] : dedekind_id R' :=
by {letI := dedekind_dvr_imp_dedekind_inv R', exact dedekind_inv_imp_dedekind_id R' f,}

/-
Time to break a lot of things !


probably morally correct: fractional ideals have prime factorization !
(→ regular ideals have prime factorization)



-/

--Noetherian iff Every non-empty set S of ideals has a maximal member.
open_locale classical

/-
Currently mathlib has the following two characteristics of Noetherian modules
(i) - Every ascending chain of ideals is eventually constant i.e. I_1 ⊂ I_2 ⊂ I_3 ⊂ … ⊂ I_n ⊂ I_{n+1} = I_n
(ii) - Every ideal is finitely generated
This is the third that mathlib does not have (pertaining to rings, perhaps to modules(?)):
(iii) - Every non-empty set S of ideals has a maximal member. i.e. if M ⊂ I, then I = R ∨ I = M
Proof of equivalence: by mathlib (i) ↔ (ii).
(ii → iii) - Start off with any ideal in S, then two cases: it is contained in another ideal (we induct)
or it is not (it is maximal and we terminate), but since eventually the first case becomes constant, we are done.

(iii → i) - Start off with a finitely generated subideal of I with only 1 generator, call it I_1
Now, add another generator, and observe that I_1 ⊂ I_2, and continue
I_1 ⊂ I_2 ⊂ I_3 ⊂ … and this chain must have a maximal ideal, and so eventually we must come to
a point such that I_{n-1} ⊂ I_n = I_{n+1}.
-/
lemma set_has_maximal [ring R'] (a : set $ ideal R') (set_nonempty : a.nonempty) : ∃ (M ∈ a), ideal.is_maximal(M) :=
begin
  sorry,
end

namespace dedekind


/-
Suppose not, then the set of ideals that are not divisible by primes is nonempty, and by set_has_maximal
must have a maximal element M.
Since M is not prime, ∃ (r,s : R-M) such that rs ∈ M.
Since r ∉ M, M+(r) > M, and since M is maximal, M+(r) and M+(s) must be divisible by some prime.
Now observe that (M+(r))(M+(s)) is divisible by some primes, but M*M ⊂ M, rM ⊂ M, sM ⊂ M, and rs ⊂ M, so
this is contained in M, but this is a contradiction.
-/
lemma ideal_contains_prime_product [dedekind_id R'] : ∀ (I : ideal R'), ∃ (P : ideal R'), P.is_prime ∧ (P∣I) :=
begin
  by_contradiction hyp,
  push_neg at hyp,
  have A := {J : ideal R' |  ∀ (P : ideal R'), P.is_prime → ¬ P ∣ J}, 
  have key : A.nonempty,
  cases hyp with I Ikey,
  use I,
  --lean fails HERE for some odd reason
  --rw set.mem_set_of_eq,
  repeat {sorry},
end
/-
For any proper ideal I, there exists an element, γ,  in K (the field of fractions of R) such that 
γ I ⊂ R.
Proof: This is really annoying.
Pick some a ∈ I, then (a) contains a product of primes, and fix P_1, … such that
P_1…P_r ⊂ (a), etc.

broken, not sure how to state it.

lemma frac_mul_ideal_contains_ring [dedekind_id R'] (I : ideal R') (h_nonzero : I ≠ ⊥) (h_nontop : I ≠ ⊤ ) : ∃ (γ : fraction_ring R'), γI ⊂ R :=
begin
  sorry,
end

-/

/-
For any ideal I, there exists J such that IJ is principal.
proof:
Let 0 ≠ α ∈ I, and let J = { β ∈ R : β I ⊂ (α )}.
We can see that J is an ideal.
and we have that IJ ⊂ (α).
Since IJ ⊂ (α), we have that A = IJ/α is an ideal of R.

If A = R, then IJ = (α) and we are done,
otherwise, A is a proper ideal, and we can use frac_mul_ideal_contains_ring
to have a γ ∈ K-R such that γ A ⊂ R. Since R is integrally closed,
it suffices to show that γ is a root of a monic polynomial over R.

We have that J ⊂ A, as α ∈ I. so γ J ⊂ γ A ⊂ R.
We make the observation that γ J ⊂ J. (rest is sketchy and annoying)

Need to refine conditions (mainly non-zero).
-/
lemma exists_ideal_prod_principal [dedekind_id R'](I : ideal R') : ∃ (J : ideal R'), (I * J).is_principal ∧ (I ≠ ⊥ ):=
begin
  sorry,
end

lemma mul_right_inj [dedekind_id R'] (A B C : ideal R') (A ≠ ⊥ ) : A * B = A * C ↔ B=C :=
begin
  symmetry,
  split,
  {intro, rw a,},
  cases exists_ideal_prod_principal(R')(A) with J Jkey,
  intro ab_eq_ac,
  have : J * A * B = J * A  * C,
  {rw [mul_assoc, ab_eq_ac,mul_assoc],},
  sorry,
end

--every ideal is generated by at most two elements of dedekind domain

--This is likely not formulated in a useful way, a list might be better, also placeholders are bad
lemma ideal_prime_factorization [dedekind_id R'] (I : ideal R') : ∃ (pset : finset $ ideal R'), ∃(powset : finset $ ℕ ), (finset.card pset = finset.card powset) ∧ (∀(P ∈  pset), ideal.is_prime(P)) ∧ false :=
begin
  sorry,  
end
end dedekind
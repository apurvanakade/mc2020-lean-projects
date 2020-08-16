import ring_theory.fractional_ideal
import ring_theory.discrete_valuation_ring
import linear_algebra.basic
import order.zorn
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

open_locale classical

class dedekind_id [integral_domain R] : Prop := 
    (noetherian : is_noetherian_ring R)
    (int_closed : is_integrally_closed_domain R)
    (max_nonzero_primes : ∀ P ≠ (⊥ : ideal R), P.is_prime → P.is_maximal)
    (not_field : ∃(I : ideal R), I ≠ ⊥ ∧ I ≠ ⊤)


theorem set_has_maximal_iff_noetherian {X : Type u} [add_comm_group X] [module R' X] : (∀(a : set $ submodule R' X), a.nonempty → ∃ (M ∈ a), ∀ (I ∈ a), M ≤ I → I=M) ↔ is_noetherian R' X := 
begin
  sorry,
end

lemma set_has_maximal [is_noetherian_ring R'] (a : set $ ideal R') (ha : a.nonempty): ∃ (M ∈ a), ∀ (I ∈ a), M ≤ I → I = M :=
begin
  sorry,
end

lemma lt_add_nonmem (I : ideal R') (a ∉ I) : I < I+ideal.span{a} :=
begin
  sorry,
end

--every nonfield has a prime ideal(?)
lemma ideal_contains_prime_product [dedekind_id R'] (I : ideal R') (gt_zero : ⊥ < I) : ∃(plist : list $ ideal R'), plist.prod ≤ I ∧ (∀(P ∈ plist), ideal.is_prime P ∧ ⊥ < P) :=
begin
  letI : is_noetherian_ring R', exact dedekind_id.noetherian,
  by_contra hyp,
  push_neg at hyp,
  let A := {J : ideal R' | ∀(qlist : list $ ideal R'), qlist.prod ≤ J → (∃ (P : ideal R'), P ∈ qlist ∧ (P.is_prime → ¬⊥ < P))},
  have key : A.nonempty,
  {use I, exact hyp,},
  rcases set_has_maximal R' A key with ⟨ M, Mkey, maximal⟩,
  rw set.mem_set_of_eq at Mkey,
  by_cases M = ⊥,
  {
    have h1 := maximal I,
    have h2 : I ∈ A, simpa,
    rw h at h1,
    have h3 := h1 h2,
    have h4 : ⊥ ≤ I,
    {cases gt_zero, exact gt_zero_left,},
    cases gt_zero,
    have := h3 h4,
    rw this at *, simpa only [],
  },
  rename h mne0,
  by_cases M.is_prime,
  {
    have mprod : [M].prod ≤  M, rw list.prod_singleton, exact le_refl M,
    rcases Mkey [M] mprod with ⟨P, pm, hp⟩,
    have : P = M, exact list.mem_singleton.mp pm,
    rw this at hp,
    have h1 := hp h,
    have : ⊥ < M, exact bot_lt_iff_ne_bot.mpr mne0,
    exact h1 this,
  },
  rename h not_prime,
  by_cases M = ⊤,
  { --this actually seems fairly hard to prove that in any nonfield ring, there exists a prime ideal
    --actually, see Krull's theorem, relatively not bad application of Zorn's
    sorry,
  },
  rename h not_top,
  unfold ideal.is_prime at not_prime,
  push_neg at not_prime,
  rcases not_prime not_top with ⟨r,s,hrs,hr,hs⟩, 
  set rm := M + ideal.span({r}) with rme,
  have hmr : M < rm,
  { exact lt_add_nonmem R' M r hr,},
  set sm := M + ideal.span({s}) with sme,
  have hms : M < sm,
  { exact lt_add_nonmem R' M s hs,},
  clear hr hs not_top,
  have main : rm*sm ≤ M,
  {--bashing simplifications, I think this would be a very nice simp tactic
    rw [rme,sme,left_distrib,right_distrib,right_distrib,← add_assoc],
    repeat {rw [ideal.add_eq_sup]},
    have blah : ∀ (x y z : ideal R'), x ≤ z → y ≤ z → x ⊔ y ≤ z, simp only [sup_le_iff], tauto,
    have part1 : M*M ≤ M, exact ideal.mul_le_left,
    have part2 : ideal.span{r} * M ≤ M, exact ideal.mul_le_left,
    have part3 : M*ideal.span{s} ≤ M, exact ideal.mul_le_right,
    have part4' : ideal.span {r} * ideal.span {s} = (ideal.span{r*s} : ideal R'),
    { unfold ideal.span, rw [submodule.span_mul_span, set.singleton_mul_singleton],},
    rw part4',
    have part4 : ideal.span{r*s} ≤ M,
    { rw ideal.span_le, simpa,},
    have h1 := blah (M*M) (ideal.span{r} * M ⊔  M * ideal.span {s} ⊔  ideal.span{r*s}) M part1,
    rw [←sup_assoc,← sup_assoc] at h1,
    apply h1,
    clear' h1 part1,
    have h1 := blah (ideal.span{r} * M) (M * ideal.span{s} ⊔ ideal.span{r*s}) M part2,
    rw [←sup_assoc] at h1,
    apply h1, clear' h1 part2,
    exact blah (M * ideal.span{s}) (ideal.span {r*s}) M part3 part4,
  },
  clear not_prime mne0 hrs,
  have key1 : rm ∉ A,
  {
    intro rma,
    cases hmr,
    have h1 := maximal rm rma hmr_left,
    have : rm ≠ M,
    { exfalso, apply hmr_right, rw h1, simp only [set.le_eq_subset],},
    exact this h1,
  },
  have key2 : sm ∉ A,
  {
    intro sma,
    cases hms,
    have h1 := maximal sm sma hms_left,
    have : sm ≠ M,
    
    { exfalso, apply hms_right, rw h1, simp only [set.le_eq_subset],},
    exact this h1,
  },
  rw set.mem_set_of_eq at key1,
  rw set.mem_set_of_eq at key2,
  push_neg at key1,
  push_neg at key2,
  rcases key1 with ⟨q1, qprod1, qp1⟩,
  rcases key2 with ⟨q2, qprod2, qp2⟩,
  let qlist := list.union q1 q2,
  have blah : qlist.prod = q1.prod * q2.prod,
  {
    clear' hms hmr rme sme main maximal key Mkey hyp gt_zero I qprod1 qprod2 qp1 qp2 A,
    simp only [qlist],
    
    sorry,
  },
  have h1 := Mkey qlist,
  repeat{sorry},
end
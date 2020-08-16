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
    (non_field : ∃(I : ideal R), ⊥ < I ∧ I < ⊤)


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

lemma nonfield_has_prime (nonfield : ∃(I: ideal R), ⊥ < I ∧ I < ⊤ ) : ∃(P : ideal R), P.is_prime ∧ ⊥ < P :=
begin
  rcases nonfield with ⟨I, gt_bot, lt_top⟩,
  have ne_top : I ≠ ⊤, exact ne_of_lt lt_top, 
  rcases ideal.exists_le_maximal I ne_top with ⟨M, maximal, gei⟩,
  have hm := ideal.is_maximal.is_prime maximal,
  have gt_bot : ⊥ < M, exact gt_of_ge_of_gt gei gt_bot,
  existsi M,
  tauto,
end

-- meta def ideal_simps := `[ideal.add_eq_sup, ideal.mul_le_left, ideal.mul_le_right, ideal.span_mul_span, ideal.span_le]

--have to prove that the list of primes is not empty
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
  { contrapose! gt_zero, subst h,
    have : I ∈ A := by simpa,
    rw (maximal I) this bot_le, simp },
  rename h mne0,
  by_cases M.is_prime,
  {
    have mprod : [M].prod ≤ M := by simp,
    rcases Mkey [M] mprod with ⟨P, pm, hp⟩,
    rw list.mem_singleton at pm,
    rw pm at hp,
    apply hp h, 
    rwa bot_lt_iff_ne_bot,
  },
  rename h not_prime,
  by_cases M = ⊤,
  { 
    have h1 : ∃(I : ideal R'), (⊥ < I ∧ I < ⊤), exact dedekind_id.non_field,
    rcases nonfield_has_prime R' h1 with ⟨P, hp, gt_zero⟩,
    have : P ≤ M, rw h, exact submodule.comap_subtype_eq_top.mp rfl,
    have pprod : [P].prod ≤ M, rwa list.prod_singleton,
    rcases Mkey [P] pprod with ⟨Q, qinp, h2 ⟩,
    have h3 : Q = P, exact list.mem_singleton.mp qinp,
    rw h3 at h2,
    exact h2 hp gt_zero,
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
    rw [rme, sme, left_distrib, right_distrib, right_distrib],
    -- Do any of these belong in the global simp set?
    -- If not, can we made an `ideal_simps` or similar, so that 
    -- `simp with ideal_simps` would close the goal.
    simpa [ideal.add_eq_sup, ideal.span_mul_span, ideal.span_le], 
   },
  clear not_prime mne0 hrs,
  have key1 : rm ∉ A, 
  { intro rma, cases hmr, apply hmr_right, 
    rw maximal rm rma hmr_left, simp },
  have key2 : sm ∉ A,
  { intro sma, cases hms, apply hms_right, 
    rw maximal sm sma hms_left, simp },
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
  have lem : qlist.prod ≤ M,
  {
    rw blah,
    have : q1.prod * q2.prod ≤ rm * sm,
    exact submodule.mul_le_mul qprod1 qprod2,
    exact le_trans this main,
  },
  rcases Mkey qlist lem with ⟨P, pinq, hp⟩,
  repeat{sorry},
end

example (a b c d : ℕ ) (hab : a ≤ b) (hcd : c ≤ d) : (a*c ≤ b*d) :=
begin
  exact nat.mul_le_mul hab hcd,

end
#check le_trans
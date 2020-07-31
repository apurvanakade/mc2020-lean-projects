import ring_theory.fractional_ideal
import ring_theory.discrete_valuation_ring
import linear_algebra.basic
universes u

variables (R : Type u) [integral_domain R] (R' : Type u) [integral_domain R']

/-
`local_id_is_id` and the other lemmas probably belong in
`ring_theory/integral_domains` or whatever

For integral domains… 
`local_id_is_id` asserts that for any submodule `S` that does not contain `0` induces an `integral_domain` on an `integral_domain`.
`local_at_prime_of_id_is_id` is the same, with the localization being at a prime
`lt_add_nonmem` proves that whenever a ∉ I, I < I+(a)
`zero_prime` is a proof that (0) is a prime ideal
`nonzero_mem_of_gt_bot` is whenever I ≠ ⊥, there exists a nonzero element of I
`ideal_mul_eq_zero` is that whenever I * J = ⊥, either I = ⊥ or J = ⊥. 
-/

theorem local_id_is_id (S : submonoid R) (zero_non_mem : ((0 : R) ∉  S)) {f : localization_map S (localization S)} : 
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

instance local_at_prime_of_id_is_id (P : ideal R') (hp_prime : P.is_prime) : 
  integral_domain (localization.at_prime P) :=
begin
  have zero_non_mem : (0 : R') ∉ P.prime_compl,
  { have := ideal.zero_mem P, simpa },
  have h1 := local_id_is_id R' P.prime_compl zero_non_mem,
  exact is_integral_domain.to_integral_domain (localization.at_prime P) h1,
  exact localization.of (ideal.prime_compl P),
end

lemma lt_add_nonmem (I : ideal R') (a ∉ I) : I < I+ideal.span{a} :=
begin
  have blah : ∀ (x y : ideal R'), x ≤ x ⊔ y, 
  { intros x y, simp only [le_sup_left],},
  split, exact blah I (ideal.span{a}),
  have blah2 : ∀ (x y z : ideal R'),  x ⊔ y ≤ z → x ≤ z → y ≤ z,
  { intros x y z, simp only [sup_le_iff], tauto,},
  have h : I ≤ I, exact le_refl I,
  rw ideal.add_eq_sup,
  intro bad,
  have h1 := blah2 I (ideal.span{a}) I bad h,
  have h2 : a ∈ ideal.span{a},
  { rw ideal.mem_span_singleton', use 1, rw one_mul,},
  have : ∀ (x ∈ ideal.span{a}), x ∈ I, simpa only [],
  exact H (this a h2),
end

lemma zero_prime : (⊥ : ideal R').is_prime :=
begin
  split,
  {
    intro,
    have h1 := (ideal.eq_top_iff_one) (⊥ : ideal R') ,
    rw h1 at a,
    have : 1 = (0 : R'), tauto,
    simpa,
  },
  {
    intros,
    have h1 : x * y = 0, tauto,
    have x_or_y0 : x = 0 ∨ y = 0,
    exact zero_eq_mul.mp (eq.symm h1),
    tauto,
  },
end

lemma nonzero_mem_of_neq_bot (I : ideal R') (gt_bot : ⊥ < I) : ∃ a : I, a ≠ 0 :=
begin
  have h := (submodule.lt_iff_le_and_exists.1 gt_bot).2,
  clear gt_bot,
  rcases h with ⟨ x, hx, key ⟩,
  use [x, hx],
  simp only [submodule.mem_bot] at key,
  simpa only [ne.def, submodule.mk_eq_zero],
end

lemma ideal_mul_eq_zero {I J : ideal R'} : (I * J = ⊥) ↔ I = ⊥ ∨ J = ⊥ :=
begin
  have hJ : inhabited J, by exact submodule.inhabited J,
  have j := inhabited.default J, clear hJ,
  split, swap,
  { intros,
    cases a,
    {rw [← ideal.mul_bot J, a, ideal.mul_comm],},
    {rw [← ideal.mul_bot I, a, ideal.mul_comm],},
  },
  intro hij,
  by_cases J = ⊥,
  right, exact h,
  left,
  rw submodule.eq_bot_iff,
  intros i hi,
  rcases J.ne_bot_iff.1 h with ⟨ j', hj, ne0⟩,
  rw submodule.eq_bot_iff at hij,
  specialize hij (i * j'),
  have := eq_zero_or_eq_zero_of_mul_eq_zero ( hij (ideal.mul_mem_mul hi hj)),
  cases this, assumption, exfalso, exact ne0 this,
end
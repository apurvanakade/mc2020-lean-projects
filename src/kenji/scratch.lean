import ring_theory.fractional_ideal
import ring_theory.discrete_valuation_ring
import linear_algebra.basic
universes u v 

variables (R : Type u) [comm_ring R] {A : Type v} [comm_ring A]
variables (K : Type u) [field K] (R' : Type u) [integral_domain R']
variables [algebra R A]

open function
open_locale big_operators

/-
Typically a good heuristic to trying to prove something like x ∈  submodule.span R' s where
x ∈ s is to first prove that {x} ⊆ s, and then try to use submodule.span_mono or smth


-/
open_locale classical

example (R' : Type u) {X : Type u}
  [integral_domain R']
  [ring R']
  [add_comm_group X]
  [module R' X] :
  is_noetherian R' X →
  ∀ (A : set (submodule R' X)),
    A.nonempty →
    (∃ (M : submodule R' X) (H : M ∈ A),
       ∀ (I : submodule R' X), I ∈ A → M ≤ I → I = M) :=
begin
  rw is_noetherian_iff_well_founded,
  intros wf A A_nonempty,
  have hA : inhabited A,
  { refine classical.inhabited_of_nonempty _, exact nonempty_subtype.mpr A_nonempty,},
  rw set.nonempty_def at A_nonempty,
  cases A_nonempty with a akey, 
  have h1 := wf.apply a,

  set r := λ (a b : submodule R' X), (a ≤ b), 

  --this is probably wrong/unnecessary
  have main : ∀ (c : set $ submodule R' X), c ⊆ A → zorn.chain r c → ∀ (y : submodule R' X), y ∈ c → (∃ (ub : submodule R' X) (H : ub ∈ A), ∀ (z : submodule R' X), z ∈ c → z ≤ ub),
  {
    intros c csubA chainc y yinc,
    contrapose! wf,
    
    --rcases hyp a akey with ⟨z ,zinc,zgta ⟩,
    --we will use h1 to drive a contradiction here
    --use induction to create an infinitely long chain --how???
    /-have h2 : ∀ (c' ⊆ c) (m ∈ c') (max : ∃(m ∈ c'), ∀ (k ∈ c'), m ≤ k → m = k), ∃(x : submodule R' X), (x ∈ c) ∧ (x > m),
    {
      intros c' c'subc m minc' max,
      have c'suba : c' ⊆ A, exact set.subset.trans c'subc csubA,
      have mina : m ∈ A, exact c'suba minc',
      have minc : m ∈ c, exact c'subc minc',
      rcases hyp m mina with ⟨x, xinc, xgtm⟩,
      use x, split, use xinc,
      have h3 := zorn.chain.total_of_refl chainc xinc minc,
      split,
      cases h3, exact id (λ (a_1 : X), false.rec (a_1 ∈ ↑m → a_1 ∈ ↑x) (xgtm h3)),
      exact h3, exact xgtm,
    },
    clear hyp, -- I think h2 is stronger than hyp
    have csubc : c ⊆ c, exact set.subset.rfl,
    have final := h2 c csubc,
    --have zina : z ∈ A, { exact csubA zinc,},
    --rcases hyp z zina with ⟨z', z'inc, z'gtz ⟩,
    --here begins the chain! finally use well_founded
    -/
    by_cases ∃(m ∈ c), ∀(k ∈ c), m ≤ k → m=k,
    {
      rcases h with ⟨m, minc, max⟩,
      have mina : m ∈ A, exact csubA minc,
      rcases wf m mina with ⟨z, zinc, zgtm⟩,
      have mztot := zorn.chain.total_of_refl chainc zinc minc,
      have : m ≤ z, cases mztot, exact id (λ (x : X), false.rec (x ∈ m → x ∈ z) (zgtm mztot)), exact mztot,
      have h0 := max z zinc this, cc,
    },
    push_neg at h,
    rw order_embedding.well_founded_iff_no_descending_seq, push_neg,
    refine nonempty.intro _,
    refine order_embedding.nat_gt _ _,
    intro n, induction n with n Mn, { assumption }, 

    
    
    --something something chain
    repeat{sorry},
  },
  have hp := zorn.zorn_partial_order₀ A main,
  rcases hp a akey with ⟨M ,MinA, Mkeyl, Mkeyr⟩,
  use M,
  split, exact MinA,
  exact Mkeyr,
end

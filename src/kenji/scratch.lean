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
  

  set r := λ (a b : submodule R' X), (a ≤ b), 
  by_contradiction h,
  push_neg at h,
  rw order_embedding.well_founded_iff_no_descending_seq at wf,
  apply wf,
  refine nonempty.intro _,
  refine order_embedding.nat_gt _ _,
  intro n,
  --somewhere around here have ∀ n : ℕ, ?m_1[n] ∈ A or something(?)
  --also I'm not entirely sure how easy/hard transitive is because it doesn't seem to show up that m_1[n] is biggest of first n
  --using h seems to be the way to get next element of chain.
  induction n with n Mn,
  use a,

  repeat {sorry},
end

import michael.simple_graph

noncomputable theory
open_locale classical

universes u
variables {V : Type u} [fintype V] 
namespace simple_graph

def empty_graph : simple_graph V := 
{ adj := λ _ _, false}

def is_subgraph (H : simple_graph V) (G : simple_graph V)  : Prop := 
∀ u v, H.adj u v → G.adj u v


variables (G : simple_graph V) 
include G

@[refl] lemma is_subgraph_self : G.is_subgraph G := by tidy


def card_edges : ℕ := fintype.card G.E

lemma card_edges_eq_zero_iff : 
  G.card_edges = 0 ↔ G = empty_graph :=
begin
  sorry
end

lemma induction_on 
  (P : simple_graph V → Prop)
  (P_empty : P empty_graph)
  (P_inductive : ∀ G ≠ empty_graph, ∃ (H : simple_graph V), 
    H.is_subgraph G ∧ 
    H.card_edges < G.card_edges ∧
    (P H → P G) ) : P G := 
begin
  by_cases h : G = empty_graph, { rwa h },
  suffices : ∀ H : simple_graph V, H.card_edges < G.card_edges → P H, 
  { have := P_inductive G h, tauto },
  induction G.card_edges using nat.strong_induction_on with k hk,
  intros H hHk, 
  by_cases H_card : H = empty_graph, { cc }, 
  rcases P_inductive H H_card with ⟨K, K_sub, K_card, hKH⟩,
  apply hKH, exact hk _ hHk _ K_card,
end
-- for every graph, there exists an edge so that P (G.erase e) → P G

def erase (e : G.E) : simple_graph V := 
{ adj := λ u v, if u ∈ e ∧ v ∈ e then false else G.adj u v,
  sym := by { unfold symmetric, intros, simp_rw [edge_symm, and_comm], cc } }

@[simp] lemma erase_adj_iff (e : G.E) (u v : V) : 
  (G.erase e).adj u v ↔ G.adj u v ∧ (u ∉ e ∨ v ∉ e) :=
by { simp [erase]; tauto, }

lemma erase_is_subgraph (e : G.E) : (G.erase e).is_subgraph G := by tidy
-- writing this down in a way that avoids nat subtraction
-- #check 
lemma card_edges_erase (e : G.E) : (G.erase e).card_edges + 1 = G.card_edges :=
begin
  sorry
end

lemma induction_on_erase
  (P : simple_graph V → Prop)
  (P_empty : P empty_graph)
  (P_inductive : ∀ G : simple_graph V, G ≠ empty_graph → 
    ∃ e : G.E, P (G.erase e) → P G)
  : P G := 
begin
  apply G.induction_on, assumption,
  intros G₁ hG₁, cases P_inductive G₁ hG₁ with e he,
  use G₁.erase e, 
  split, { apply erase_is_subgraph },
  split, linarith [G₁.card_edges_erase e],
  assumption,
end

end simple_graph

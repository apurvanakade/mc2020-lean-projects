import michael.simple_graph

universes u
variables {V : Type u} [fintype V]
namespace simple_graph

def empty_graph : simple_graph V := sorry

variables (G : simple_graph V)
include G
def is_subgraph (H : simple_graph V) : Prop := sorry

def card_edges : ℕ := sorry

lemma card_edges_eq_zero_iff : 
  G.card_edges = 0 ↔ G = empty_graph :=
begin
  sorry
end

lemma induction_on 
  (G : simple_graph V) 
  (P : simple_graph V → Prop)
  (P_empty : P empty_graph)
  (P_inductive : ∀ G, G ≠ empty_graph → ∃ (H : simple_graph V), 
    H.is_subgraph G ∧ 
    H.card_edges < G.card_edges ∧
    (P H → P G) )
  :
  P G
  := sorry
-- for every graph, there exists an edge so that P (G.erase e) → P G

def erase (e : G.E) : simple_graph V := sorry

lemma erase_is_subgraph (e : G.E) : (G.erase e).is_subgraph G :=
sorry
-- writing this down in a way that avoids nat subtraction
lemma card_edges_erase (e : G.E) : (G.erase e).card_edges + 1 = G.card_edges :=
sorry

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

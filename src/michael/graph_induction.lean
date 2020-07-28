import michael.simple_graph

universes u
variables {V : Type u} [fintype V]
namespace simple_graph

def empty_graph : simple_graph V := sorry

def is_subgraph (G H : simple_graph V) : Prop := sorry

def card_edges (G : simple_graph V) : ℕ := sorry

lemma simple_graph.induction_on 
  (G : simple_graph V) 
  (P : simple_graph V → Prop)
  (P_inductive : ∀ G, ∃ (H : simple_graph V), 
    H.is_subgraph G ∧ 
    H.card_edges ≤ G.card_edges ∧
    P H → P G)
  (P_empty : P empty_graph)
  :
  P G
  := sorry
-- for every graph, there exists an edge so that P (G.erase e) → P G


end simple_graph

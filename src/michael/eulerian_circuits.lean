import .basic
import data.nat.parity
import data.finset

noncomputable theory

universes u
variables {V : Type u} [fintype V] (G : graph V)
open graph finset

def KonigsbergBridges : multigraph (fin 4) :=
multigraph_of_edges [(0,1), (0,2), (0,3), (1,2), (1,2), (2,3), (2,3)]

def KonigsbergBridgesProblem : Prop :=
¬ is_Eulerian KonigsbergBridges

namespace graph
include G
def degree (v : V) : ℕ := 
begin
  have nbrs := neighbours G v,
  have x : nbrs.finite,
  exact set.finite.of_fintype(nbrs),
  have fin_nbrs := set.finite.to_finset x,
  exact fin_nbrs.card,
end
-- degree for undirected graphs

def crossed (v : V) {x y : V} (p : G.path x y) : ℕ :=
begin
  have in_edge := {w : V | G.edge w v ∧ mem (G.edge w v) p}
end
-- number of times v is in an edge in path x y

def has_eulerian_path : Prop := ∃ x y : V, ∃ p : G.path x y, is_Eulerian p

-- lemma tours_degree_distinct (x, y : V) : (x ≠ y) → (∀ z : V, z ≠ x ∧ z ≠ y → )


lemma has_eulerian_path_iff : 
  G.has_eulerian_path ↔ card (filter {v : V | ¬ nat.even (G.degree v)} univ) ∈ ({0, 2} : finset ℕ) :=
sorry
-- iff the number of vertices of odd degree is 0 or 2

end graph
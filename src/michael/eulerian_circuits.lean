import .basic
import data.nat.parity
import data.finset

noncomputable theory

universes u
variables {V : Type u} [fintype V] (G : graph V)
open graph graph.path finset

def KonigsbergBridges : multigraph (fin 4) :=
multigraph_of_edges [(0,1), (0,2), (0,3), (1,2), (1,2), (2,3), (2,3)]

def KonigsbergBridgesProblem : Prop :=
¬ is_Eulerian KonigsbergBridges

namespace graph
include G
def degree (v : V) : ℕ := sorry

def has_eulerian_path : Prop := ∃ x y : V, ∃ p : G.path x y, p.is_Eulerian


lemma has_eulerian_path_iff : 
  G.has_eulerian_path ↔ card (filter {v : V | ¬ nat.even (G.degree v)} univ) ∈ ({0, 2} : finset ℕ) :=
sorry
-- iff the number of vertices of odd degree is 0 or 2

end graph
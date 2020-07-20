import .basic
import data.nat.parity
import data.finset
import .simple_graph
import tactic

noncomputable theory
open_locale classical

universes u
variables {V : Type u} [fintype V] (G : simple_graph V)
open graph finset

def KonigsbergBridges : multigraph (fin 4) :=
multigraph_of_edges [(0,1), (0,2), (0,3), (1,2), (1,2), (2,3), (2,3)]

-- def KonigsbergBridgesProblem : Prop :=
-- ¬ is_Eulerian KonigsbergBridges


open simple_graph
namespace simple_graph

-- namespace graph
-- include G
-- def degree (v : V) : ℕ := 
-- begin
--   have nbrs := neighbours G v,
--   have x : nbrs.finite,
--   exact set.finite.of_fintype(nbrs),
--   have fin_nbrs := set.finite.to_finset x,
--   exact fin_nbrs.card,
-- end
-- degree for undirected graphs

def crossed (v : V) {x y : V} (p : G.path x y) : ℕ :=
begin
  have in_edge := finset.filter {w : V | if h : G.adj w v then G.mem h p else false } univ,
  exact finset.card in_edge,
end
-- number of times v is in an edge in path x y

def has_eulerian_path : Prop := ∃ x y : V, ∃ p : G.path x y, G.is_Eulerian p

lemma no_edge_in_nil {d x y : V} (h : G.adj x y) : ¬ G.mem h (path.nil d) :=
begin
  by_contradiction,
  cases a,
end

-- no edges contained in the nil path

lemma path_crossed {x y : V} (p : G.path x y) (z : V) : ((x = y) → nat.even (G.crossed z p)) ∧ 
((x ≠ y) → ¬ nat.even (G.crossed x p) → ¬ nat.even (G.crossed y p) 
→ (z ≠ x ∧ z ≠ y → nat.even (G.crossed z p))) :=
begin
  induction p with d hd,
  split,
  intro eq_self,
  have cross_zero : G.crossed z (path.nil d) = 0,
  unfold crossed,
  rw finset.card_eq_zero,
  convert finset.filter_false _,
  ext, simp, split_ifs,
  exact no_edge_in_nil G h,
  exact not_false,
  exact classical.dec_pred (λ (a : V), false),
  rw cross_zero,
  norm_num,
  intro neq_self,
  exfalso,
  apply neq_self, refl,
  sorry,
end
-- if x=y, all vertices have crossed = even, else all vertices except x and y have crossed = odd

lemma has_eulerian_path_iff : 
  G.has_eulerian_path ↔ card (filter {v : V | ¬ nat.even (G.degree v)} univ) ∈ ({0, 2} : finset ℕ) :=
sorry
-- iff the number of vertices of odd degree is 0 or 2

end simple_graph
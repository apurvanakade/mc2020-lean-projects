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

lemma crossed_add_edge {x y z : V} (e : G.adj x y) (p : G.path y z) (w : V) :
(w = x ∨ w = y) → (G.crossed w p + 1 = G.crossed w (e :: p)) :=
begin
  sorry,
end
-- adding an edge adds 1 to crossed if the edge contains the vertex

lemma path_crossed {x y : V} (p : G.path x y) (z : V) : 
nat.even (G.crossed z p) ↔ (x = y) ∨ (z ≠ x ∧ z ≠ y)
:=
begin
  -- induction p with d hd using h,
  induction p with d hd,
  -- base case
  { suffices : G.crossed z (path.nil d) = 0, simp [this],
    erw finset.card_eq_zero,
    convert finset.filter_false _,
    ext, simp, split_ifs,
    { exact no_edge_in_nil G h },
    { exact not_false },
    { apply_instance }},
  -- induction step
  cases p_ih with even_to_eq eq_to_even,
  split,
  intro cross_even,
  by_cases p_s = p_t,
  have fl_even : (G.crossed z p_l).even,
  apply eq_to_even,
  left, exact h,
  right,
  split,
  contrapose! fl_even,
  rw fl_even,
  have one_cross : G.crossed hd p_l + 1 = G.crossed hd (p_e :: p_l),
  apply crossed_add_edge,
  left, refl,
  have cross_one_even : (G.crossed hd p_l + 1).even,
  rw one_cross,
  rw fl_even at cross_even,
  exact cross_even,
  exact nat.even_succ.mp cross_one_even,
  contrapose! fl_even,
  rw fl_even,
  have one_cross : G.crossed p_t p_l + 1 = G.crossed p_t (p_e :: p_l),
  apply crossed_add_edge,
  right, rw h,
  have cross_one_even : (G.crossed p_t p_l + 1).even,
  rw one_cross,
  rw fl_even at cross_even,
  exact cross_even,
  exact nat.even_succ.mp cross_one_even,
  

  sorry,
end
-- if x=y, all vertices have crossed = even, else all vertices except x and y have crossed = odd

lemma has_eulerian_path_iff : 
  G.has_eulerian_path ↔ card (filter {v : V | ¬ nat.even (G.degree v)} univ) ∈ ({0, 2} : finset ℕ) :=
sorry
-- iff the number of vertices of odd degree is 0 or 2

end simple_graph
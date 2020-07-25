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
finset.card $ finset.filter {w : V | if h : G.adj w v then G.mem h p else false } univ

-- number of times v is in an edge in path x y

def has_eulerian_path : Prop := ∃ x y : V, ∃ p : G.path x y, G.is_Eulerian p

lemma no_edge_in_nil {d x y : V} (h : G.adj x y) : ¬ G.mem h (path.nil d) :=
by rintro ⟨⟩

@[simp] lemma path.mem_cons {x s t u v: V} (e : G.adj x s) (h : G.adj u v) (p : G.path s t) :
 G.mem h (e :: p) ↔ u = x ∧ v = s ∨ G.mem h p :=
begin
  split,
  intro m, 
  by_cases eq : u = x ∧ v = s,
  {left, exact eq},
  right,
  push_neg at eq,
  induction m with d hd,
  sorry,
end

-- no edges contained in the nil path
lemma crossed_add_edge {x y z : V} (e : G.adj x y) (p : G.path y z) (w : V) :
(w = x ∨ w = y) → ( G.crossed w (e :: p) = G.crossed w p + 1) :=
begin
  intro h, delta crossed, 
  convert card_insert_of_not_mem _, 
  swap, { apply_instance }, swap, exact x,
  { ext a, rw mem_filter, 
    simp only [set.set_of_app_iff, true_and, mem_filter, mem_insert, mem_univ, path.mem_cons],  
    split_ifs with haw, swap, { simp, contrapose! haw, subst haw, sorry },
    { sorry }},
  { sorry },
end
-- adding an edge adds 1 to crossed if the edge contains the vertex

lemma crossed_add_non_edge {x y z : V} (e : G.adj x y) (p : G.path y z) (w : V) :
(w ≠ x ∧ w ≠ y) → ( G.crossed w (e :: p) = G.crossed w p) :=
begin
  intro h, delta crossed, congr, ext a,
  split_ifs with haw, swap, { tauto },
  split, { tidy },
  intro hp, apply mem.tail _ _ _ hp,
end
-- adding an edge adds 0 to crossed if the edge does not contain the vertex

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
  -- implies condition
  cases p_ih with even_to_eq eq_to_even,
  have one_cross : G.crossed hd p_l + 1 = G.crossed hd (p_e :: p_l), { symmetry, apply crossed_add_edge, tauto },
  split,
  { intro cross_even,
    by_cases h : p_s = p_t,
    have fl_even : (G.crossed z p_l).even,
    { apply eq_to_even, left, exact h },
    right, split, 
    { contrapose! fl_even, rw fl_even,
      suffices cross_one_even : (G.crossed hd p_l + 1).even, { rwa ← nat.even_succ },
      rw one_cross, rwa fl_even at cross_even },
    { contrapose! fl_even, rw fl_even,
      have one_cross : G.crossed p_t p_l + 1 = G.crossed p_t (p_e :: p_l),
      { symmetry, apply crossed_add_edge, right, rw h },
      rw ← nat.even_succ, convert cross_even, rw [fl_even, ← one_cross]},

    by_cases h1 : hd = p_t, { tauto },
    right, split,
    contrapose! cross_even,
    rw [cross_even, ← one_cross, nat.even_succ, ← cross_even], 
    push_neg, apply eq_to_even,
    right, split, { rw cross_even, exact ne_of_edge G p_e },
    rwa cross_even,
    contrapose! cross_even,
    have zero_cross : G.crossed z p_l = G.crossed z (p_e :: p_l),
    symmetry, apply crossed_add_non_edge,
    rw cross_even, tauto, 
    rw ← zero_cross,
    tauto,},

  -- impliedby direction
  { intro eq_cond,
    by_cases z = hd,
    { rw h, rw ← one_cross,
      have cross_odd : ¬ (G.crossed hd p_l).even,
      by_contradiction, rw ← h at a,
      have eq_cond1 := even_to_eq(a), 
      cases eq_cond, cases eq_cond1,
      { rw ← eq_cond1 at eq_cond, contrapose! eq_cond, exact G.ne_of_edge p_e },
      { cases eq_cond1, rw eq_cond at h, exact eq_cond1_right(h) },
      { cases eq_cond, exact eq_cond_left(h) },
      exact nat.even_succ.mpr cross_odd },
    by_cases h1 : z = p_t,
    { exfalso, 
      cases eq_cond, rw eq_cond at h, exact h(h1), 
      cases eq_cond, exact eq_cond_right(h1) },
    by_cases h2 : z = p_s,
    have cross_one : G.crossed z (p_e :: p_l) = G.crossed z p_l + 1,
    { apply crossed_add_edge, right, exact h2 },
    have cross_odd : ¬ (G.crossed z p_l).even, { finish },
    { rw cross_one, exact nat.even_succ.mpr cross_odd },
    have cross_zero : G.crossed z (p_e :: p_l) = G.crossed z p_l,
    { apply crossed_add_non_edge, split, exact h, exact h2 },
    finish},
end
-- if x=y, all vertices have crossed = even, else all vertices except x and y have crossed = odd
lemma path_crossed' {x y : V} (p : G.path x y) (z : V) : 
nat.even (G.crossed z p) ↔ (x = y) ∨ (z ≠ x ∧ z ≠ y)
:=
begin
  induction p with d a s t has p hp,
  { suffices : G.crossed z (path.nil d) = 0, simp [this],
    erw finset.card_eq_zero,
    convert finset.filter_false _, swap, { apply_instance },
    ext, split_ifs,
    { have := no_edge_in_nil G h, simpa }, tauto },
  have has' := G.ne_of_edge has,
  split; 
  { by_cases hz : z = a ∨ z = s,
    { rw [crossed_add_edge, nat.even_succ, hp], assumption',
      try { rintro ⟨rfl, h⟩, tauto },
      cases hz; { rw hz at *, tauto }},
    push_neg at hz, 
    rw [crossed_add_non_edge, hp], assumption',
    rintro ⟨rfl, h⟩; tauto },
end

lemma degree_eq_crossed {x y : V} (p : G.path x y) : 
G.is_Eulerian p → ∀ z : V, G.degree z = G.crossed z p :=
begin
  intro h,
  -- induction p with d a s t has p hp, 
  -- I think we need induction on the number of edges?
  -- I don't think induction is possible here because the inductive hypothesis give us zero info
  -- Maybe just expanding definitions?
  unfold degree crossed,
  refine congr_fun _, ext a, congr,
  ext, simp only [true_and, mem_filter, neighbor_iff_adjacent, mem_univ], 
  rw [set.set_of_app_iff, edge_symm], 
  split_ifs with h1, swap, { tauto },
  suffices : G.mem h1 p, { simpa [h1] },
  cases h with t m,
  tauto,
end

lemma has_eulerian_path_iff : 
  G.has_eulerian_path ↔ card (filter {v : V | ¬ nat.even (G.degree v)} univ) ∈ ({0, 2} : finset ℕ) :=
begin
  split,
  { rintro ⟨x, y, p, hep⟩,
    have deg_cross := G.degree_eq_crossed p hep,
    simp at *, 
    by_cases x = y,
    { left, convert finset.filter_false _,
      { ext, simp [deg_cross, path_crossed, h] },
      { apply_instance } },
    { right,
      have : finset.card {x, y} = 2, { rw [card_insert_of_not_mem, card_singleton], rwa mem_singleton },
      convert this, ext, 
      suffices : ¬(G.degree a).even ↔ a = x ∨ a = y, convert this; { simp; refl },
      rw [deg_cross, path_crossed'], simp [h]; tauto,
    }},
  intro h, simp only [mem_insert, card_eq_zero, mem_singleton] at h, 
  -- I think we need induction on the number of edges?
  sorry,
end
-- iff the number of vertices of odd degree is 0 or 2

end simple_graph
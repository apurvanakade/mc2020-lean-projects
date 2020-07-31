import data.nat.parity
import data.finset
import .path
import .graph_induction
import tactic

noncomputable theory
open_locale classical

open simple_graph
namespace simple_graph

universes u
variables {V : Type u} [fintype V] {G : simple_graph V}
open finset



/-- number of times v is in an edge in path x y -/
-- should be number of times v is in an edge of p
def path.crossed (v : V) (p : G.path) : ℕ :=
p.edges.countp $ λ e, v ∈ e

variables (G)
def has_eulerian_path : Prop := ∃ p : G.path, p.is_Eulerian
variables {G}

-- no edges contained in the nil path
lemma crossed_cons {s v : V} (e : G.E) (p : G.path) (w : V) (hp : p.head ∈ e) (hs : s ∈ e) (hsv):
(p.cons e hp hs hsv).crossed v = p.crossed v + if v = s ∨ v = p.head then 1 else 0 :=
begin
  dsimp [path.crossed, path.cons],
  split_ifs with h, 
  { cases h; simp [h, hs, hp] },
  suffices : v ∉ e, { simp [this] },
  rw e.mem_iff hs, push_neg, split, tauto,
  contrapose! h, right, 
  rw h, symmetry, rw e.eq_other_iff, tauto,
end
-- adding an edge adds 1 to crossed if the edge contains the vertex

-- lemma crossed_add_non_edge {x y z : V} (e : G.adj x y) (p : G.path y z) (w : V) :
-- (w ≠ x ∧ w ≠ y) → ( G.crossed w (e :: p) = G.crossed w p) :=
-- begin
--   intro h, delta crossed, congr, ext a,
--   split_ifs with haw, swap, { tauto },
--   split, { tidy },
--   intro hp, apply mem.tail _ _ _ hp,
-- end
-- -- adding an edge adds 0 to crossed if the edge does not contain the vertex

-- if x=y, all vertices have crossed = even, else all vertices except x and y have crossed = odd
lemma path_crossed (p : G.path) (z : V) : 
nat.even (p.crossed z) ↔ p.is_cycle ∨ (z ≠ p.head ∧ z ≠ p.last)
:=
begin
  induction p with d a s t hp,
  split,
  simp at *,
  sorry,
  -- induction p with d a s t has p hp,
  -- { suffices : G.crossed z (path.nil d) = 0, simp [this],
  --   erw finset.card_eq_zero,
  --   convert finset.filter_false _, swap, { apply_instance },
  --   ext, split_ifs,
  --   { have := no_edge_in_nil G h, simpa }, tauto },
  -- have has' := G.ne_of_edge has,
  -- split; 
  -- { by_cases hz : z = a ∨ z = s,
  --   { rw [crossed_add_edge, nat.even_succ, hp], assumption',
  --     try { rintro ⟨rfl, h⟩, tauto },
  --     cases hz; { rw hz at *, tauto }},
  --   push_neg at hz, 
  --   rw [crossed_add_non_edge, hp], assumption',
  --   rintro ⟨rfl, h⟩; tauto },
end

lemma degree_eq_crossed (v : V) (p : G.path) (hp : p.is_Eulerian): 
G.degree v = p.crossed v :=
begin
  unfold degree, unfold path.crossed,
  
  sorry,
  -- intro h,
  -- induction p with d a s t has p hp, 
  -- I think we need induction on the number of edges?
  -- I don't think induction is possible here because the inductive hypothesis give us zero info
  -- Maybe just expanding definitions?
  -- unfold degree crossed,
  -- refine congr_fun _, ext a, congr,
  -- ext, simp only [true_and, mem_filter, mem_univ, mem_neighbor_finset],
  -- rw [set.set_of_app_iff, edge_symm], 
  -- split_ifs with h1, swap, { tauto },
  -- suffices : G.mem h1 p, { simpa [h1] },
  -- cases h with t m,
  -- tauto,
end

lemma has_eulerian_path_iff [nonempty V] : 
  G.has_eulerian_path ↔ card (filter {v : V | ¬ nat.even (G.degree v)} univ) ∈ ({0, 2} : finset ℕ) :=
begin
  split,
  { intro hep, cases hep with p e,
    simp at *,
    by_cases p.is_cycle,
    { left, convert finset.filter_false _,
      { ext, 
        have deg_cross := degree_eq_crossed x p e, rw deg_cross,
        simp [path_crossed, h],
        },
      { apply_instance } },
    { right,
      have : finset.card {p.head, p.last} = 2, { rw [card_insert_of_not_mem, card_singleton], rwa mem_singleton },
      convert this, ext,
      suffices : ¬(G.degree a).even ↔ a = p.head ∨ a = p.last, convert this; { simp; refl },
      have deg_cross := degree_eq_crossed a p e, rw [deg_cross, path_crossed], simp [h]; tauto,
    }},
    refine G.induction_on _ _ _,
    { intro, inhabit V, use path.empty (arbitrary _), sorry },
    clear G, intros G hG0,
    by_cases (filter {v : V | ¬(G.degree v).even} univ).card = 0,
    { sorry },
    by_cases (filter {v : V | ¬(G.degree v).even} univ).card = 2,
    { sorry },
    use empty, split, exact empty_is_subgraph G,

    -- convert G.induction_on _ _ _, refl,
  
  
  
  -- { rintro ⟨x, y, p, hep⟩,
  --   have deg_cross := G.degree_eq_crossed p hep,
  --   simp at *, 
  --   by_cases x = y,
  --   { left, convert finset.filter_false _,
  --     { ext, simp [deg_cross, path_crossed, h] },
  --     { apply_instance } },
  --   { right,
  --     have : finset.card {x, y} = 2, { rw [card_insert_of_not_mem, card_singleton], rwa mem_singleton },
  --     convert this, ext, 
  --     suffices : ¬(G.degree a).even ↔ a = x ∨ a = y, convert this; { simp; refl },
  --     rw [deg_cross, path_crossed'], simp [h]; tauto,
  --   }},
  -- intro h, simp only [mem_insert, card_eq_zero, mem_singleton] at h, 
  -- I think we need induction on the number of edges?
  
  sorry,
end
-- iff the number of vertices of odd degree is 0 or 2

def KonigsbergBridge : simple_graph (fin 4) := 
begin
  sorry,
end


theorem KonigsbergBridgesProblem : ¬ has_eulerian_path KonigsbergBridge :=
begin
  sorry,
end


end simple_graph
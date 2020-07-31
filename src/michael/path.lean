-- authorship note: we pulled things from mathlib:hedetniemi without looking carefully at authorship.
-- we'll have to backsolve for the author list later
import michael.simple_graph
import tactic.omega
import tactic.apply_fun

universes u
variables {V : Type u}

section list

lemma list.cons_nth_le_succ
  {α : Type*} {hd : α} (tl : list α) 
  (n : ℕ) (hn : n + 1 < (tl.cons hd).length) 
  (h_auto : n < tl.length := by tidy)
  :
(tl.cons hd).nth_le (n + 1) hn = tl.nth_le n h_auto := rfl

lemma list.cons_nth_le_succ'
  {α : Type*} (l : list α) 
  (n : ℕ) (hn : n + 1 < l.length) 
  (h_auto : n < l.tail.length)
  :
l.nth_le (n + 1) hn = l.tail.nth_le n h_auto := 
by { cases l, { cases hn }, simp; refl }

@[simp] lemma list.nth_le_succ_tail
  {α : Type*} (l : list α) 
  (n : ℕ) (hn : n < l.tail.length)
  (h_auto : n + 1 < l.length)
  -- (h_auto : n + 1 < l.length := by { simp at hn, omega })
   :
l.nth_le (n + 1) h_auto = l.tail.nth_le n hn := 
by { cases l, tidy }

@[simp] lemma list.tail_nth_le_zero
  {α : Type*} (l : list α) [inhabited α]
  (h_auto : 0 < l.length) :
list.nth_le l 0 h_auto = l.head := 
by { cases l, { cases h_auto }, tidy, }


end list

namespace simple_graph
variables (G : simple_graph V)

/-- Morally, a path is an alternating list of vertices and edges, 
  with incidences between adjacent objects -/
@[ext] structure path :=
(head : V)
(tail : list V)
(edges : list G.E)
(length_eq : edges.length = tail.length)
(adj : ∀ (n : ℕ) (hn : n < edges.length), 
  let u := (list.cons head tail).nth_le n (by { simp; omega }) in
  let v := (list.cons head tail).nth_le (n + 1) (by { simp, cc }) in
  u ≠ v ∧ u ∈ edges.nth_le n hn ∧ v ∈ edges.nth_le n hn)


namespace path
variables {G} 
variables (p : G.path)

section classical
open_locale classical
/-- The last vertex in p. -/
noncomputable def last : V := if h : p.tail = list.nil then p.head else p.tail.last h

end classical

/-- The ordered list of all vertices in p, starting at p.head and ending at p.sink. -/
def vertices : list V := p.head :: p.tail 

/-- The number of edges in p. -/
def length : ℕ := p.tail.length

@[simp] lemma tail_length_eq : p.tail.length = p.length := rfl
@[simp] lemma edges_length_eq : p.edges.length = p.length :=  by simp [p.length_eq]


lemma head_ne_tail_head [inhabited V] (h : p.tail ≠ list.nil) : p.head ≠ p.tail.head :=
begin
  rcases p.adj 0 _ with ⟨hp, _⟩, dsimp at hp, convert hp, 
  cases hp1 : p.tail, 
  { contradiction }, 
  { simp [hp1] },
  { revert h, rw ← list.length_pos_iff_ne_nil, simp }, 
end

-- variables {s t : V}

variables {p}
/-- p.edge_mem e holds if e is an edge along path p. -/
def edge_mem (e : G.E) (p : G.path) : Prop := e ∈ p.edges
-- this instance doesn't fire and I don't know why
instance has_mem_edge : has_mem G.E G.path := 
{ mem := edge_mem }

/-- p.vertex_mem v holds if v is a vertex along path p. -/
def vertex_mem (v : V) (p : G.path) : Prop := v ∈ p.vertices
instance has_mem_vertices : has_mem V G.path := 
{ mem := vertex_mem }
variables (p)

/-- The empty path based at vertex v. -/
def empty (v : V) : G.path :=
{ head := v,
  tail := list.nil,
  edges := list.nil,
  length_eq := rfl,
  adj := by rintros _ ⟨_⟩ }

instance [inhabited V] : inhabited G.path := { default := empty (arbitrary V) }

lemma edge_mem_empty {v : V} (e : G.E) : ¬ (empty v).edge_mem e :=
by simp [empty, edge_mem]

lemma vertex_mem_empty {u v : V} : u ∈ (@empty _ G v) ↔ u = v :=
by { unfold has_mem.mem vertex_mem, simp [empty, vertices], apply or_false }

/-- p.cons e hp hs is the path extending `p` by edge `e`. -/
def cons {s : V} (e : G.E) (hp : p.head ∈ e) (hs : s ∈ e) (hsp : s ≠ p.head) : G.path :=
{ head := s,
  tail := p.vertices, 
  edges := list.cons e p.edges,
  length_eq := by { simp [vertices] },
  adj := begin
    intros n hn _ _,
    cases n, { simp, tauto },
    simp; apply p.adj,
  end }

@[simp] lemma edge_mem_cons {s : V} (hd e : G.E) (hp : p.head ∈ hd) (hs : s ∈ hd) (hsp : s ≠ p.head) : 
  (p.cons hd hp hs hsp).edge_mem e ↔ e = hd ∨ p.edge_mem e :=
by simp [path.cons, path.vertices, edge_mem]

@[simp] lemma vertex_mem_cons {v s : V} (hd : G.E) (hp : p.head ∈ hd) (hs : s ∈ hd) (hsp : s ≠ p.head) : 
  v ∈ (p.cons hd hp hs hsp) ↔ v = s ∨ v ∈ p :=
by refl

@[simp] lemma cons_length {s : V} (hd : G.E) (hp : p.head ∈ hd) (hs : s ∈ hd) (hsp : s ≠ p.head) : 
  (p.cons hd hp hs hsp).length = p.length + 1 :=
by { unfold cons length, simp [vertices] }

@[simp] lemma cons_vertices {s : V} (hd : G.E) (hp : p.head ∈ hd) (hs : s ∈ hd) (hsp : s ≠ p.head) : 
  (p.cons hd hp hs hsp).vertices = list.cons s p.vertices :=
by { dsimp [vertices, cons], simp }

lemma edges_eq_nil_iff : p.edges = list.nil ↔ p.tail = list.nil :=
by rw [← list.length_eq_zero, p.length_eq, list.length_eq_zero]

lemma length_eq_zero_iff_eq_empty : p.length = 0 ↔ p = empty p.head :=
begin
  erw list.length_eq_zero,
  split; intro h, swap, rw h, simp [empty],
  ext, work_on_goal 2 {rw ← edges_eq_nil_iff at h},
  any_goals {simp [empty, h]},
end

lemma cases_on' [nonempty V] : 
  (∃ v, p = empty v) ∨
  ∃ (tl : G.path) v e (hs : tl.head ∈ e) (hv : v ∈ e) (hvp : v ≠ tl.head), p = tl.cons e hs hv hvp :=
begin
  inhabit V,
  cases hp : p.edges with hd tl, 
  { left, use p.head, ext, { simp [empty] }, 
    { suffices : p.tail = list.nil, { simp [empty, this] },
      rwa edges_eq_nil_iff at hp },
    simp [hp, empty] }, 
  have hp_nil : ¬ p.edges = list.nil, { simp [hp] },
  rw edges_eq_nil_iff at hp_nil,

  rcases p.adj 0 _ with ⟨hvs, hv, hs⟩, simp only [list.nth_le, zero_add] at hs, 
  repeat { rw list.nth_le_zero at * }, 
  set q : G.path := { head := p.tail.head,
    tail := list.tail p.tail,
    edges := list.tail p.edges,
    length_eq := by simp [p.length_eq],
    adj := _},
  swap, { intros, have := p.adj (n + 1) (by { simp only [list.length_tail] at hn, exact nat.add_lt_of_lt_sub_right hn, }), 
    simp only [list.nth_le] at this ⊢, 
    cases this with huv this,
    cases hp_tail : p.tail with p_hd p_tl, { contradiction },
    dsimp [u,v], simp [hp_tail],   split, 
    { contrapose! huv, symmetry, convert huv using 1; simp [hp_tail, huv]; refl },
    -- simp [hp_tail, this],
    -- rw list.tail_nth_le, 
    convert this using 2,
    any_goals { simp [hp_tail]; refl },
    -- { rw list.cons_head_tail hp_nil, refl }, 
    iterate 2 { rwa list.cons_nth_le_succ' },
    },
  right, use [q, p.head, hd], 
  simp only [hp, list.head] at hs hv, swap, { simp [hp] },
  dsimp, use [hs, hv], split,
  ext, 
  { simp [path.cons] },
  { dsimp [q, path.cons, path.vertices], rwa list.cons_head_tail, },
  { dsimp [q, path.cons], simp [hp] }, 
  revert hvs, simp,
end

lemma induction_on [nonempty V] 
  (P : G.path → Prop)
  (P_empty : ∀ v, P $ empty v) 
  (P_inductive : ∀ p e hs {v} (hv : v ∈ e) (hsv), P p → P (p.cons e hs hv hsv)) : 
P p :=
begin
  suffices : ∀ k (q : G.path), q.length = k → P q, { apply this p.length, refl },
  intro k, induction k with k hk, { intros, convert P_empty _, rwa ← length_eq_zero_iff_eq_empty },
  intro q, rcases q.cases_on' with ⟨_,rfl⟩|⟨_,_,_,_,_,_,rfl⟩, { intro, apply P_empty },
  intro, apply P_inductive, apply hk, simp at a, omega,
end

/-- p.is_cycle if p starts and ends in the same place. -/
def is_cycle : Prop := p.head = p.last

/-- p.is_trail if p has no repeated edges. -/
def is_trail : Prop := list.nodup p.edges

/-- p.is_Eulerian if p hits each edge exactly once. -/
def is_Eulerian : Prop := ∀ e : G.E, p.edge_mem e

end path

end simple_graph
#lint-
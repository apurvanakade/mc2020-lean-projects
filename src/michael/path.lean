import michael.simple_graph

universes u
variables {V : Type u}

namespace simple_graph
variables (G : simple_graph V)

-- TODO: this could literally be implemented with a list and a pairwise adjacent constraint. 
-- Then we'd have more lemmas available and `mem_cons` would be ~just an application of of the same for lists. 
/-- A path is an ordered list of vertices where consecutive elements are adjacent. -/
inductive path : V → V → Type u
| nil  : Π (h : V), path h h
| cons : Π {h s t : V} (e : G.adj h s) (l : path s t), path h t

notation a :: b := path.cons a b

/-- For e an edge and p a path, G.mem e p is true if the edge lies on the path. -/
inductive mem : Π {w x y z : V} (e : G.adj x y) (p : G.path w z), Prop
| head : ∀ {x y z} (e : G.adj x y) (p : G.path y z), mem e (e :: p)
| head_symm : ∀ {x y z} (e : G.adj x y) (p : G.path y z), mem (G.sym e) (e :: p)
| tail : ∀ {v w x y z} (e : G.adj v w) (e' : G.adj x y) (p : G.path w z) (m : mem e' p), mem e' (e :: p)

inductive is_trail : Π {x y} (p : G.path x y), Prop
| nil : ∀ (x), is_trail (path.nil x)
| cons : ∀ {x y z} (e : G.adj x y) (p : G.path y z) (h : ¬ G.mem e p), is_trail (e :: p)

def is_Eulerian {x y} (p : G.path x y) : Prop :=
G.is_trail p ∧ ∀ {x' y'} (e : G.adj x' y'), G.mem e p

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
  induction m, tidy,
  sorry,
  sorry,
end

end simple_graph
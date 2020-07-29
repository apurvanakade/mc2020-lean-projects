import michael.simple_graph

universes u
variables {V : Type u}

namespace simple_graph
variables (G : simple_graph V)

-- TODO: this could literally be implemented with a list and a pairwise adjacent constraint. 
-- Then we'd have more lemmas available and `mem_cons` would be ~just an application of of the same for lists. 
/-- A path is an ordered list of vertices where consecutive elements are adjacent. -/
inductive path : V → V → Type u
| nil  : Π (v : V), path v v 
| cons : Π {v s t : V} (e : G.E) (hv : v ∈ e) (hs : s ∈ e) (l : path s t), path v t

-- notation a :: b := path.cons a b
namespace path
variables {G}
/-- For e an edge and p a path, G.mem e p is true if the edge lies on the path. -/
inductive mem : Π {s t : V} (e : G.E) (p : G.path s t), Prop
| nil : ∀ {v} (e : G.E) (h : false), mem e (path.nil v)
| head : ∀ {v s t : V} (e : G.E) (hv : v ∈ e) (hs : s ∈ e) (tl : G.path v t), mem e (tl.cons e hs hv)
| tail : ∀ {v s t : V} (e e' : G.E) (hv : v ∈ e) (hs : s ∈ e) (tl : G.path v t) (h : mem e' tl) , mem e' (tl.cons e hs hv)

instance has_mem_edge {s t : V} : has_mem G.E (G.path s t) := 
{ mem := mem }

/-- For e an edge and p a path, G.mem e p is true if the edge lies on the path. -/
inductive vmem : Π {s t : V} (v : V) (p : G.path s t), Prop
| nil : ∀ v, vmem v (path.nil v)
| head : ∀ {v s t : V} (p : G.path s t), vmem s p
| tail : ∀ {v s t : V} (e : G.E) (hv : v ∈ e) (hs : s ∈ e) (tl : G.path v t) (h : vmem v tl), vmem v (tl.cons e hs hv)

instance has_mem_vertex {s t : V} : has_mem V (G.path s t) := 
{ mem := vmem }

inductive is_trail : Π {s t} (p : G.path s t), Prop
| nil : ∀ v, is_trail (path.nil v)
| tail : ∀ {v s t} (e : G.E) (hv : v ∈ e) (hs : s ∈ e) (tl : G.path v t) (h : ¬ tl.mem e), is_trail (tl.cons e hs hv)

def is_Eulerian {x y} (p : G.path x y) : Prop :=
p.is_trail ∧ ∀ e, p.mem e

lemma no_edge_in_nil {d x y : V} (e : G.E) : ¬ (path.nil d).mem e :=
by rintro ⟨⟩

lemma path.mem_cons
 {v s t : V} (e hd : G.E) (hv : v ∈ e) (hs : s ∈ e) (tl : G.path v t) :
 (path.cons e hs hv tl).mem e ↔ e = hd ∨ tl.mem e :=
begin
  by_cases h : e = hd, { simp [h, mem.head] },
  split, intro a, 
  cases a,
  sorry,
  sorry,
end

end path
end simple_graph

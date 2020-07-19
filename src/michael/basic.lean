-- definitions copied from mathlib.hedetniemi/graph_theory/basic.lean & paths.lean

import data.equiv.basic
import logic.relation
import data.fintype.basic
import data.set.finite
import tactic

noncomputable theory

/-!
# Definitions of graphs
-/

universe variables v v₁ v₂ v₃ u u₁ u₂ u₃ u₄

structure directed_multigraph (V : Type u) :=
(edge : V → V → Sort v)

def directed_multigraph.vertices {V : Type u} (G : directed_multigraph V) := V

structure multigraph (V : Type u) extends directed_multigraph.{v} V :=
(inv : Π (x y), edge x y ≃ edge y x)

def multigraph_of_edges {n : ℕ} (e : list (fin n × fin n)) : multigraph (fin n) :=
{ edge := λ x y, fin (e.countp (λ p, p = (x, y) ∨ p = (y, x))),
  inv := λ x y, by { dsimp, convert equiv.refl _, funext, rw or_comm, } }

structure directed_graph (V : Type u) extends directed_multigraph.{0} V.

def directed_graph.vertices {V : Type u} (G : directed_graph V) := V

structure graph (V : Type u) extends multigraph.{0} V :=
(symm {} : symmetric edge)
(inv := λ x y, equiv.of_iff ⟨@symm _ _, @symm _ _⟩)

notation x `~[`G`]` y := G.edge x y

namespace graph
variables {V : Type u}
variables (G : graph V)
variables [fintype V]

def vertices (G : graph V) := V

def edge.symm {G : graph V} {x y : V} (e : x ~[G] y) : y ~[G] x := G.symm e

def is_linked (G : graph V) (x y : V) : Prop :=
relation.refl_trans_gen G.edge x y

def is_connected (G : graph V) : Prop :=
∀ ⦃x y⦄, G.is_linked x y

def is_loopless (G : graph V) : Prop :=
∀ ⦃x⦄, ¬ (x ~[G] x)

def neighbours (G : graph V) (v: V) : set V :=
begin
  have nbrs := {w : V | G.edge v w}, 
  exact nbrs,
end

def out_degree (G: graph V) (v : V) : ℕ :=
begin
  have nbrs := neighbours G v,
  have x : nbrs.finite,
  exact set.finite.of_fintype(nbrs),
  have fin_nbrs := set.finite.to_finset x,
  exact fin_nbrs.card,
end

def in_degree (G: graph V) (v : V) : ℕ :=
begin
  have out_nbrs := {w : V | G.edge w v},
  have x : out_nbrs.finite,
  exact set.finite.of_fintype(out_nbrs),
  exact (set.finite.to_finset x).card,
end

lemma ne_of_edge {G : graph V} (h : G.is_loopless) {x y : V} (e : x ~[G] y) :
  x ≠ y :=
by { rintro rfl, exact h e }
end graph

variables {V : Type u} (G : directed_multigraph.{v} V)
variables [fintype V]

namespace directed_multigraph

inductive path : V → V → Type (max v u)
| nil  : Π (h : V), path h h
| cons : Π {h s t : V} (e : G.edge h s) (l : path s t), path h t

notation a :: b := path.cons a b
notation `p[` l:(foldr `, ` (h t, path.cons h t) path.nil _ `]`) := l

abbreviation tour (x : V) : Type (max v u) := path G x x

end directed_multigraph

namespace multigraph

abbreviation path (H : multigraph.{v} V) := directed_multigraph.path H.to_directed_multigraph

end multigraph

open directed_multigraph

namespace path

variables {H : multigraph.{v} V}

inductive mem : Π {w x y z : V} (e : H.edge x y) (p : H.path w z), Prop
| head : ∀ {x y z} (e : H.edge x y) (p : H.path y z), mem e (e :: p)
| head_symm : ∀ {x y z} (e : H.edge x y) (p : H.path y z), mem (H.inv x y e) (e :: p)
| tail : ∀ {v w x y z} (e : H.edge v w) (e' : H.edge x y) (p : H.path w z) (m : mem e' p), mem e' (e :: p)

inductive is_trail : Π {x y} (p : H.path x y), Prop
| nil : ∀ (x), is_trail (path.nil x)
| cons : ∀ {x y z} (e : H.edge x y) (p : H.path y z) (h : ¬ mem e p), is_trail (e :: p)

def is_Eulerian {x y} (p : H.path x y) : Prop :=
is_trail p ∧ ∀ {x' y'} (e : H.edge x' y'), mem e p

end path

open path

open graph

variables (H : multigraph.{v} V)

def is_Eulerian : Prop :=
∃ {x : V} (p : tour H.to_directed_multigraph x), is_Eulerian p

def KonigsbergBridges : multigraph (fin 4) :=
multigraph_of_edges [(0,1), (0,2), (0,3), (1,2), (1,2), (2,3), (2,3)]

def KonigsbergBridgesProblem : Prop :=
¬ is_Eulerian KonigsbergBridges

theorem in_degree_out_degree_equal_tour (G: graph V) (x : V) (t : tour G.to_directed_multigraph x) 
: (is_Eulerian t) → (∀ y : V, G.out_degree y = G.in_degree y) :=
begin
  sorry,
end

theorem KonigsbergNotEulerian : ¬ is_Eulerian KonigsbergBridges :=
begin
  by_contradiction,
  cases a with V ex_path,
  cases ex_path with t d,
  sorry, 
end
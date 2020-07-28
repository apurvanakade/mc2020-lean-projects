import .basic
import .eulerian_circuits

noncomputable theory
open_locale classical

-- universes u
-- variables {V : Type u} [fintype V]
open graph 
open finset

def KonigsbergBridges : multigraph (fin 4) :=
multigraph_of_edges [(0,1), (0,2), (0,3), (1,2), (1,2), (2,3), (2,3)]

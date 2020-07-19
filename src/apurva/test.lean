import data.complex.basic 
import linear_algebra.finite_dimensional
import tactic 

universes u
variables {n : Type u} [fintype n]


instance hn_fd : finite_dimensional ℂ (n → ℂ) := 
begin 
  apply_instance,
end 

local notation `Vec` := (n → ℂ)

instance hn_fd' : finite_dimensional ℂ Vec := 
begin 
  apply_instance,
end 

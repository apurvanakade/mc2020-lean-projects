# Tactics Writing 


- Some mathlib tactics that may have easy improvements:
`group`, `noncomm_ring`, `mfld_set_tac`
- New tactics that mathlib wants:
something like `ring`, but which knows about groebner basis methods
- Try to do proofs in `algebra/big_operators.lean` with a tactic that can do basic `finset` induction starting with something like
  ```lean
  meta def finset_induction := `[  classical,
    induction s using finset.induction with p hp s hs, { simp },
    rw [sum_insert, sum_insert], assumption',
    convert hs,]
  ```

## Resources 

- [Rob Lewis' lectures on Metaprogramming in Lean](https://www.youtube.com/playlist?list=PLlF-CfQhukNnq2kDCw2P_vI5AfXN7egP2)
- [Exercises from Lean for the Curious Mathematician 2020
 workshop](https://leanprover-community.github.io/lftcm2020/exercises.html)


# Eigenvalues and Diagonalization

## August 15, 2020
Completely new proof using the theorems from https://github.com/abentkamp/spectral/blob/master/src/eigenvector.lean

There we have the theorem :
`lemma generalized_eigenvector_span` 
which states that the generalized eigenvectors of a linear operator `f` span the entire space and hence provide a basis. 

from here to get the spectral theorem we need to prove two things. let `M` be a normal matrix and let `f` be the corresponding linear operator.

1. two eigenvectors `v` and `w` corresponding different eigenvalues are orthogonal. the proof of this is here: https://math.stackexchange.com/questions/778946/prove-that-if-a-is-normal-then-eigenvectors-corresponding-to-distinct-eigenva
2. prove proposition 7.2 here which says that every generalized eigenvector of a normal operator is an eigenvector https://www.maa.org/sites/default/files/pdf/awards/Axler-Ford-1996.pdf
3. putting all these (unit) eigenvectors together into a matrix gives us a unitary matrix `U`
4. we can rephrase the above conclusions as saying that `U ^* M U` is upper triangular
5. we need to show that `U^* M U` is also normal
6. finally, here is a proof that every upper triangular normal matrix is diagonal https://math.stackexchange.com/questions/1762563/if-a-is-normal-and-upper-triangular-then-it-is-diagonal

## July 15, 2020

Looks like there are two different "linear maps" in mathlib - matrices and linear operator. 

Basic things that are missing 
  - Direct sums of vector spaces 
  - Hilbert spaces 
  - Eigenvalues and eigenspaces of linear operators 
  - Eigenvalues ond eigenspaces of matrices
  
## July 17, 2020

**New plan:** (based on Zulipchat conversations) prove spectral theorem for normal *matrices*. 

> **Spectral Theorem for Normal Matrices.** Let `A` be a normal matrix i.e. `A` is a complex valued matrix such that `A A^* = A^* A` then there exists a unitary matrix `U` (i.e. `U U^* = 1`) and a diagonal matrix `D` such that `A = UDU^*`. 

**Proof.**

Let `A` be a normal matrix and let `U` be unitary matrix. 
* `U^*AU` is a normal matrix.
* If a normal matrix is upper triangular then it is diagonal.
* Let `U` be a unitary matrix whose columns are eigenvector of `A`. Then `U^*AU` is upper triangular.
* Prove that such a `U` exists.

To prove the last step there needs to be a lot of basic theorems setup about eigenvalues and eigenvectors so that seems like a good place to start.
Also, need the following definitions: Minor of a matrix, Normal matrices, Unitary matrices, eigenvalues, eigenvectors
And optionally should define symmetric, Skew Symmetric, Orthogonal, Hermitian, Skew Hermitian matrices.


## July 19, 2020
It might be difficult to construct an eigenbasis. Here's a more direct approach. 
Let `A` be a normal matrix. 
* Prove that `A` has at least one eigenvalue and eigenvector, `k` and `v`.
* Show that `v` can be extended to a unitary matrix `U`.
* Show that `A = U B U^*` where `B` is a matrix with `B_{00} = k`, `B_{ij} = 0` if `i = 0, j > 0` or `i > 0, j = 0`. 
  Let `B'` be the `(n-1) \times (n-1)` minor of `B`.
* By induction, `B' = V D V^*` where `V` is unitary and `D` is diagonal. 
* Rest of the proof is algebraic manipulations.



## References 

* https://leanprover-community.github.io/mathlib_docs/linear_algebra/nonsingular_inverse.html
* https://leanprover-community.github.io/mathlib_docs/linear_algebra/matrix.html
* [LftCM2020: Linear algebra - Anne Baanen's
 lecture video](https://youtu.be/EnZvGCU_jpc)
* http://math.fau.edu/schonbek/LinearAlgebra/lafa13normalspectra.pdf

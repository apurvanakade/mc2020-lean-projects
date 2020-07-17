# Eigenvalues and Diagonalization



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


## References 

* https://leanprover-community.github.io/mathlib_docs/linear_algebra/nonsingular_inverse.html
* https://leanprover-community.github.io/mathlib_docs/linear_algebra/matrix.html
* [LftCM2020: Linear algebra - Anne Baanen's
 lecture video](https://youtu.be/EnZvGCU_jpc)

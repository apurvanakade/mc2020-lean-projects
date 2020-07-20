# Foundations
## Dedekind domains
They are integral domains with the following equivalent definitions (among several others, see wikipedia).

##### Definition 1
Noetherian, integrally closed rings such that any nonzero prime ideal is maximal.

##### Definition 2
A Noetherian ring such that the localization at any nonzero prime ideal is a discrete valuation ring.

##### Defintion 3
A ring such that any of its fractional ideals is invertible.

#### Useful Facts

**Lemma 1** (0) $p = pR_p \cap R$
*Proof:*
(1) Since $1 \in R_p$, we have that $p \subset pR_p \cap R$.
(2) If $xy^{-1} \not\in p$, and $xy^{-1} \in R$, then $yx^{-1} \in R_p$, so $x \not\in pR_p$, otherwise $y \in pR_p$, a contradiction.

*Primitive:*
(0) ??? $R_P$ should be given by `localization.at_prime(P)` but the coercion of $P$ seems to be fairly difficult to manage. Maybe something along the lines of `let f : ideal R' \to _ := localization_map.at_prime(K)`?
(1) How does one deal with subsets? For $P \subset PR_P \cap R$, this expression seems to have a lot of coercions.
(2) Seems straightforward.

<!---
jstark to kenji:

Are you talking about intersection and inclusion as submodules or subsets? i think mathlib already has the lattive structure for submodules.
-->

**Lemma 2** (0) For ideals of $R_p$, $J = (J \cap R) R_p$.
*Proof:*
(1) For any $xy^{-1} \in J$, then $x \in J \cap R$, and since $y^{-1} \in R_p$, $xy^{-1} \in (J \cap R) R_p \implies J \subset (J \cap R) R_p$.
(2) Trivially, $(J \cap R) R_p \subset J$.

*Primitive:*
(0) Lemma 1 (0) is close enough
(1) For all $xy^{-1} there exists an element of $(J \cap R)R_p$ (use projections), $x \in (J \cap R), \ y^{-1} \in R_p$. 
(2) Essentially the argument is that $J \cap R \subset J$. It seems hard to formalize.

**Ring Cancellation** (0) Let $S$ be a ring, and $R$ be a subring, then for any ideal $I \subset S$, $(I \cap R)S \subset I$.
???

**DVRs are Integrally closed** (most likely in laughinggas/DVR)

#### $1 \implies 2$
*Proof*
(1) Every ideal of $R_p$ is of the form $IR_p, \ I \subset R$. The generating set of $I$ over $R$ is also a generating set of $IR_p$ over $R_p$, so $R_p$ is Noetherian.
(2)  
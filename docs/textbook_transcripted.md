# Cell Decompositions

We wish to think of a cell complex as a topological space built up inductively by
attaching cells of increasing dimensions along their boundaries. To specify more
specifically what we mean by "attaching cells along their boundaries," suppose $X$ is
a nonempty topological space, $\{D_\alpha^n\}$ is an indexed collection of closed
$n$-cells for some fixed $n \ge 1$, and for each $\alpha$, we are given a continuous
map $\varphi_\alpha : \partial D_\alpha^n \to X$. Letting $\varphi_\alpha : D_\alpha^n
\to X$ be the map whose restriction to each $\partial D_\alpha^n$ is $\varphi_\alpha$,
we can form the adjunction space
$X \cup_{\varphi_\alpha} \left(\bigsqcup_\alpha D_\alpha^n\right)$ (Fig. 5.2). Any
space homeomorphic to such an adjunction space is said to be obtained from $X$ by
attaching $n$-cells to $X$. Example 3.7(b) shows that $S^2$ can be obtained by
attaching a single $2$-cell to $S^1$. If $Y$ is obtained from $X$ by attaching
$n$-cells, it follows from Proposition 3.77 that we can view $X$ as a closed subspace
of $Y$, and as a set, $Y$ is the disjoint union of $X$ and a collection of disjoint
open $n$-cells, one for each $\alpha$.

It is possible to define a cell complex as a space formed inductively by starting
with a nonempty discrete space $X_0$, attaching some $1$-cells to it to form a space
$X_1$, attaching some $2$-cells to it to form a new space $X_2$, and so on. Many
authors do in fact define cell complexes this way, and it is a good way to think about
them in order to develop intuition about their properties. However, the theory works
more smoothly if we start out by describing what we mean by a cell decomposition of a
given topological space; only later will we come back and describe how to construct
cell complexes inductively "from scratch" (see Theorem 5.20).

Any space formed inductively by the procedure described above will be a union of
disjoint subspaces homeomorphic to open cells of various dimensions. Thus, at its most
basic, a cell decomposition of a space $X$ is a partition of $X$ into open cells
(i.e., a collection of disjoint nonempty subspaces of $X$ whose union is $X$, and each
is homeomorphic to $B^n$ for some $n$). But without some restriction on how the cells
fit together, such a decomposition tells us nothing about the topology of $X$. For
example, if we partition $\mathbf{R}^2$ into vertical lines, then each line is an open
$1$-cell, but the decomposition has very little to do with the topology of the plane.
This can be remedied by insisting that the boundary of each open cell be attached in
some "reasonable" way to cells of lower dimension.

Here are the technical details of the definition. If $X$ is a nonempty topological
space, a cell decomposition of $X$ is a partition of $X$ into subspaces that are open
cells of various dimensions, such that the following condition is satisfied: for each
$n$-cell $e \subset X$ and each $n \ge 1$, there exists a continuous map $\varphi$ from
some closed $n$-cell $D$ into $X$ called a characteristic map for $e$ that restricts
to a homeomorphism from $\operatorname{Int} D$ onto $e$ and maps $\partial D$ into the
union of all cells of dimension $\le n-1$. A cell complex is a Hausdorff space $X$
together with a specific cell decomposition of $X$. (The Hausdorff condition is
included here to rule out various pathologies and because, as we showed below,
inductive construction of cell complexes automatically yields Hausdorff spaces.)

In the definition of cell decomposition, we could have stipulated that the domain of
each characteristic map be the closed unit ball $B^n$ itself; but for many purposes it
is convenient to allow more general closed cells such as the interval $[0,1]$ or convex
polygonal regions in the plane.

Given a cell complex $(X, \mathcal{E})$, the open cells in $\mathcal{E}$ are typically
just called the cells of $X$. Be careful: although each $e \in \mathcal{E}$ is an open
cell, meaning that it is homeomorphic to $B^n$ for some $n$, it is not necessarily an
open subset of $X$. By the closed map lemma and Proposition 2.30, the image of a
characteristic map for $e$ is equal to $e$, so each cell is precompact in $X$; but its
closure might not be a closed cell, because the characteristic map need not be
injective on the boundary.

A finite cell complex is one whose cell decomposition has only finitely many cells. A
cell complex is called locally finite if the collection of open cells is locally
finite. By Lemma 4.74, this is equivalent to the requirement that the collection
$\overline{\mathcal{E}} = \{ \overline{e} : e \in \mathcal{E} \}$ be locally finite.

As we saw below, it is perfectly possible for a given space to have many different
cell decompositions. Technically, the term cell complex refers to a space together
with a specific cell decomposition of it (though not necessarily with specific
choices of characteristic maps). As usual in such situations, we will sometimes say
"$X$ is a cell complex" to mean that $X$ is a space endowed with a particular cell
decomposition.

# CW Complexes

For finite complexes (which are adequate for most of our purposes), the definitions we
have given so far serve well. But infinite complexes are also useful in many
circumstances, and for infinite complexes to be well behaved, two more restrictions
must be added.

First we need the following definition. Suppose $X$ is a topological space, and
$\mathcal{B}$ is any family of subspaces of $X$ whose union is $X$. To say that the
topology of $X$ is coherent with $\mathcal{B}$ means that a subset $U \subset X$ is
open in $X$ if and only if its intersection with each $B \in \mathcal{B}$ is open in
$B$. It is easy to show by taking complements that this is equivalent to the
requirement that $U$ is closed in $X$ if and only if $U \cap B$ is closed in $B$ for
each $B \in \mathcal{B}$. (In either case, the "only if" implication always holds by
definition of the subspace topology on $B$, so it is the "if" part that is
significant.)

For example, if $(X_\alpha)$ is an indexed family of topological spaces, the disjoint
union topology on $\bigsqcup_\alpha X_\alpha$ is coherent with the family
$\{ X_\alpha \}$, though each of the $X_\alpha$ is a subspace of the disjoint union. A
space is compactly generated (see Chapter 4 for the definition) if and only if its
topology is coherent with the family consisting of all of its compact subsets.

The next proposition expresses some basic properties of coherent topologies.

**Proposition 5.2.1.** Suppose $X$ is a topological space whose topology is coherent
with a family $\mathcal{B}$ of subspaces.

(a) If $Y$ is another topological space, then a map $f : X \to Y$ is continuous if and
only if $f|_B$ is continuous for every $B \in \mathcal{B}$.

(b) The map $\bigsqcup_{B \in \mathcal{B}} B \to X$ induced by inclusion of each set
$B \to X$ is a quotient map.

*Exercise 5.3.* Prove the preceding proposition.

A CW complex is cell complex $(X, \mathcal{E})$ satisfying the following additional
conditions:

(C) The closure of each cell is contained in a union of finitely many cells.

(W) The topology of $X$ is coherent with the family of closed subspaces
$\{ \overline{e} : e \in \mathcal{E} \}$.

A cell decomposition of a space $X$ satisfying (C) and (W) is called a CW
decomposition of $X$. The letters C and W come from the names originally given to
these two conditions by the inventor of CW complexes, J. H. C. Whitehead: condition
(C) was called closure finiteness, and the coherent topology in condition (W) was
called the weak topology associated with the subspaces $\{ \overline{e} : e \in
\mathcal{E} \}$.

The term has fallen into disuse in this context, because the phrase weak topology is
now most commonly used to describe the coarsest topology for which some family of
maps $f_\alpha$ from a space are all continuous, while the coherent topology is the
finest topology for which the inclusion maps of the sets $\overline{e}$ into $X$ are
all continuous (see Problem 5-5).

For locally finite complexes (and thus all finite ones), conditions (C) and (W) are
automatic, as the next proposition shows.

**Proposition 5.4.** Let $X$ be a Hausdorff space, and let $\mathcal{E}$ be a cell
decomposition of $X$. If $\mathcal{E}$ is locally finite, then it is a CW
decomposition.

*Proof.* To prove condition (C), observe that for each $e \in \mathcal{E}$, every
point of $\overline{e}$ has a neighborhood that intersects only finitely many cells of
$\mathcal{E}$. Because $\overline{e}$ is compact, it is covered by finitely many such
neighborhoods.

To prove (W), suppose $A \subset X$ is a subset whose intersection with $\overline{e}$
is closed in $\overline{e}$ for each $e \in \mathcal{E}$. Given $x \in X - A$, let $W$
be a neighborhood of $x$ that intersects the closures of only finitely many cells, say
$\overline{e}_1, \ldots, \overline{e}_m$. Since $A \cap \overline{e}_i$ is closed in
$\overline{e}_i$, this implies that

$$
W - A = W - \bigl((A \cap \overline{e}_1) \cup \cdots \cup (A \cap \overline{e}_m)\bigr)
$$

is a neighborhood of $x$ contained in $X - A$. Thus $X - A$ is open, so $A$ is closed.
$\square$

Suppose $X$ is a CW complex. If there is an integer $n$ such that all of the cells of
$X$ have dimension at most $n$, then we say $X$ is *finite-dimensional*; otherwise, it
is *infinite-dimensional*. If it is finite-dimensional, the dimension of $X$ is the
largest $n$ such that $X$ contains an $n$-cell. (The fact that this is well defined
depends on the theorem on invariance of dimension.) Of course, a finite complex is
always finite-dimensional.

Here is one situation in which open cells actually are open subsets.

**Proposition 5.5.** Suppose $X$ is an $n$-dimensional CW complex. Then every $n$-cell of
$X$ is an open subset of $X$.

*Proof.* Suppose $e$ is an $n$-cell of $X$. If $\varphi : D^n \to X$ is a characteristic
map for $e$, then $\varphi$, considered as a map onto $X_e$, is a quotient map by the
closed map lemma. Since $\varphi^{-1}(e) = \operatorname{Int} D^n$ is open in $D^n$, it
follows that $e$ is open in $X_e$. On the other hand, if $Y$ is any union of $n$-cells
of $X$, then $Y = X - Z$, where $Z$ is a union of finitely many cells of dimension less
than $n$. Since those cells cover $X - Y$, it follows that $Y$ is open in $X$. Thus
every $n$-cell is open in $X$. $\square$

A subcomplex of $X$ is a subspace $Y \subset X$ that is a union of cells of $X$, such
that if $Y$ contains a cell, it also contains its closure. It follows immediately from
the definition that the union and the intersection of any collection of subcomplexes
of $X$ are also subcomplexes. For each nonnegative integer $n$, we can let $X^n$ be the
subspace $X^n \subset X$ consisting of the union of all cells of dimension less than or
equal to $n$; it follows that $X^n$ is an $n$-dimensional subcomplex of $X$.

**Theorem 5.6.** Suppose $X$ is a CW complex and $Y$ is a subcomplex of $X$. Then $Y$ is
closed in $X$, and with the subspace topology and the cell decomposition that it
inherits from $X$, it is a CW complex.

*Proof.* Obviously $Y$ is Hausdorff, and by definition it is the disjoint union of its
cells. Let $\mathcal{E}_Y$ denote such a cell. Since $Y \subset X$, finitely many cells
of $X$ that have nontrivial intersections with it must also be cells of $Y$, so
condition (C) is automatically satisfied by $Y$. In addition, any characteristic map
$\varphi : D^n \to X$ for a cell $e$ in $Y$ also serves as a characteristic map for $Y$.

To prove that $Y$ satisfies condition (W), suppose $S \subset Y$ is a subset such that
$S \cap e$ is closed in $e$ for every cell $e$ of $Y$. Let $e$ be a cell of $X$ that is
contained in $Y$. We know that $e$ is contained in the union of finitely many cells of
$Y$; some of these, say $e_1, \ldots, e_k$, might be contained in $Y$. Then
$Z = e_1 \cup \cdots \cup e_k \subset Y$, and since $Z$ is closed in $Y$ it follows that
$Z$ is closed in $X$. Then

$$
S \cap Z = (S \cap e_1) \cup \cdots \cup (S \cap e_k)
$$

is closed in $Z$, hence in $X$. Since $S \cap e = (S \cap Z) \cap e$, it follows that
$S \cap e$ is closed in $e$. Thus $S$ is closed in $X$, and hence in $Y$. Finally, to
show that $Y$ is closed in $X$, just apply the argument in the preceding paragraph with
$S = Y$. $\square$

**Proposition 5.7.** If $X$ is any CW complex, the topology of $X$ is coherent with the
collection of subcomplexes $\{ X^n : n \ge 0 \}$.

*Proof.* Problem 5.7. $\square$

An open cell $e \subset X$ is called a *regular cell* if it admits a characteristic map
that is a homeomorphism onto its image. For example, Proposition 5.1 shows that the
interior of a compact convex subset of $\mathbf{R}^n$ (if nonempty) is a regular
$n$-cell in $\mathbf{R}^n$. If $M$ is an $n$-manifold, every regular coordinate ball (as
defined in Chapter 4) is a regular $n$-cell in $M$. Every $0$-cell is a regular cell by
convention. For a regular cell, we can always take the inclusion map $\tilde{e} \hookrightarrow X$
as a characteristic map.

Note that if we wish to show a certain open cell $e \subset X$ is a regular cell, it is
not sufficient to show only that $e$ is a closed cell; it is necessary to exhibit a
characteristic map that is a homeomorphism onto its image. For example, the set
$\{ (x,0) : 0 < x < 1 \}$ is an open interval in $\mathbf{R}^2$ whose closure is a
closed $2$-cell, but it is not a regular cell, because it is not homeomorphic to
$S^1$.

A CW complex is called a *regular CW complex* or *regular cell complex* if each of its
cells is regular, and the closure of each cell is a finite subcomplex.

**Example 5.8 (CW complexes).**

(a) A $0$-dimensional CW complex is just a discrete space; it is a finite complex if
and only if it is a finite set.

(b) Recall that a bouquet of circles is a wedge sum of the form $S^1 \vee \cdots \vee
S^1$ (Example 3.54). Such a wedge sum has a cell decomposition with one $0$-cell (the
base point), and a $1$-cell for each of the original circles; for the characteristic
maps, we can take the compositions

$$
I^1 \xrightarrow{f_i} S_i^1 \xrightarrow{i_i} \bigsqcup S^1 \xrightarrow{q} S^1 \vee \cdots \vee S^1,
$$

where $q$ is the quotient map of Example 3.56 and $i_i$ is the inclusion of the $i$th
copy of $S^1$ into the disjoint union.

(c) In general, a CW complex of dimension less than or equal to $1$ is called a graph.
(This use of the word "graph" is explained in Chapter 3.) Each $0$-cell of the complex
is called a vertex (plural: vertices), and each $1$-cell is called an edge. A graph is
said to be finite if its associated CW complex is finite. Graphs have many applications
in both pure and applied mathematics, and are among the most extensively studied of
objects in the mathematical disciplines known as combinatorics. We will study some of
their topological properties in Chapter 10.

(d) Let us construct a regular cell decomposition of $S^n$. Note first that $S^0$,
being a finite discrete space, is already a regular $0$-dimensional cell complex with
two cells. Suppose by induction that we have constructed a regular cell decomposition
of $S^{n-1}$ with two cells in each dimension $0, \ldots, n-1$. Now consider $S^n$ as a
subspace of $S^{n+1}$ (the subset where the $x_{n+1}$ coordinate is zero), and note
that the open upper and lower hemispheres of $S^n$ are regular $n$-cells whose
boundaries lie in $S^{n-1}$. The cell decomposition of $S^{n-1}$ together with these
new $n$-cells yields a regular cell decomposition of $S^n$ with exactly two cells in
each dimension $0$ through $n$. For each $k = 0, \ldots, n$, the $k$-skeleton of this
complex is $S^k$.

(e) Here is a different cell decomposition of $S^n$, with one $0$-cell and one $n$-cell
and no others. The $0$-cell is the "north pole," $(0, \ldots, 0, 1)$, and the
characteristic map for the $n$-cell is the map $q : B^n \to S^n$ of Example 4.55, which
collapses $\partial B^n$ to a single point.

(f) A regular cell decomposition of $\mathbf{R}$ is obtained by defining the $0$-cells
to be the integers, and the $1$-cells to be the intervals $(n, n+1)$ for $n \in
\mathbf{Z}$, with characteristic maps $\varphi_n : [n, n+1] \to \mathbf{R}$ given by
inclusion. Conditions (C) and (W) are automatic because the decomposition is locally
finite.

Here are two examples of cell decompositions that are not CW decompositions.

**Example 5.9.** Let $X \subset \mathbf{R}^2$ be the union of the closed line segments
from the origin to the points $(1, 1/n)$ for $n \in \mathbf{N}$, with the subspace
topology (Fig. 5.3). Define a cell decomposition of $X$ by declaring the $0$-cells to
be $(0,0)$, $(1,0)$, and the points $(1, 1/n)$, and the $1$-cells to be the line
segments joining them to the origin. This is easily seen to be a cell decomposition
that satisfies condition (C). However, it does not satisfy condition (W), because the
set $\{ (1, 1/n) : n \in \mathbf{N} \}$ has a closed intersection with the closure of
each cell, but is not closed in $X$ because it has the origin as a limit point.

**Example 5.10.** Let $X$ be a cell decomposition of $B^2$ with countably many $0$-cells
at the points $(2^{-n}, 0)$, $n \in \mathbf{N}$, countably many $1$-cells consisting of
the open arcs between the $0$-cells, and a single $2$-cell consisting of the interior
of the disk (Fig. 5.4). Condition (W) is satisfied for the simple reason that the
closure of the $2$-cell is $B^2$ itself; so any set that has a closed intersection with
each $\overline{e}$ is automatically closed in $B^2$. But condition (C) does not hold.

As you read the theorems and proofs in the rest of this chapter, it will be a good
exercise to think about which of the results fail to hold for these two examples.

# Topological Properties of CW Complexes

Many basic topological properties of CW complexes, such as connectedness and
compactness, can be read off easily from their CW decompositions.

We begin with connectedness. It turns out that this information is already contained
in the $1$-skeleton: the next theorem shows, among other things, that a CW complex is
connected if and only if its $1$-skeleton is connected.

**Theorem 5.11.** For a CW complex $X$, the following are equivalent.

(a) $X$ is path-connected.

(b) $X$ is connected.

(c) The $1$-skeleton of $X$ is connected.

(d) Some $n$-skeleton of $X$ is connected.

*Proof.* Obviously, (a) $\Rightarrow$ (b) and (c) $\Rightarrow$ (d), so it suffices to
show that (b) $\Rightarrow$ (c) and (d) $\Rightarrow$ (a).

To prove (b) $\Rightarrow$ (c), we prove the contrapositive. Suppose that
$X^1 = X_1' \cup X_1''$ is a disconnection of the $1$-skeleton of $X$. We show by
induction on $n$ that each $n$-skeleton $X^n = X_n' \cup X_n''$ is a disconnection. As
a notational convenience, let $X_1' \subset X^1$ and $X_1'' \subset X^1$ be the given
disconnection. Suppose that $X^{n-1} = X_{n-1}' \cup X_{n-1}''$ is a disconnection of
$X^{n-1}$. For each $n$-cell $e$ of $X$, let $\varphi : D^n \to X$ be a characteristic
map. Its restriction to $\partial D^n$ is a continuous map into $X^{n-1}$ since
$\partial D^n \subset D^n$ maps into $X^{n-1}$, and because $\partial D^n$ is connected,
its image must lie in $X_{n-1}'$ or $X_{n-1}''$. Thus $\overline{e}$ is contained in
$X_{n-1}'$ or $X_{n-1}''$. Divide the $n$-cells into two disjoint collections
$\{ e_\alpha^n \}$ and $\{ e_\beta^n \}$ according to whether their closures intersect
$X_{n-1}'$ or $X_{n-1}''$, respectively, and let

$$
X_n' = X_{n-1}' \cup \left(\bigcup e_\alpha^n\right), \qquad
X_n'' = X_{n-1}'' \cup \left(\bigcup e_\beta^n\right).
$$

Clearly $X_n'$ is the disjoint union of $X_{n-1}'$ and $\bigcup e_\alpha^n$, and both
sets are nonempty because $X_{n-1}'$ and $X_{n-1}''$ are nonempty by the inductive
hypothesis. If $e$ is any cell of $X^n$, its closure is entirely contained in one of
these two sets, so $X_n'$ and $X_n''$ are separated (and closed in $X^n$). This
completes the induction.

Since $X = \bigcup_n X^n$ and $X' = \bigcup_n X_n'$, $X'' = \bigcup_n X_n''$, as before,
$X = X' \cup X''$ and both sets are nonempty. By the same argument as above, if $e$ is
any cell of $X$ and of any dimension, its closure must be contained in one of these
sets. Thus $X'$ and $X''$ are both open and closed in $X$, so $X$ is disconnected.

To prove (d) $\Rightarrow$ (a), suppose $X$ is a CW complex whose $n$-skeleton is
connected for some $n \ge 0$. We show by induction on $k$ that $X_k$ is
path-connected for each $k \ge n$. It then follows that $X$ is a union of the
path-connected subsets $X_k$ for $k \ge n$, all of which have points of $X_n$ in
common, so $X$ is path-connected.

First we need to show that $X_n$ itself is path-connected. If $n = 0$, then $X_n$ is
discrete and connected, so it is a singleton and thus certainly path-connected.
Otherwise, choose any point $x_0 \in X_n$, and let $S_n$ be the path component of
$X_n$ containing $x_0$. For each cell $e$ of $X_n$, note that $\overline{e}$ is the
continuous image (under a characteristic map) of a path-connected space, so it is
path-connected. Thus if $\overline{e}$ has a nontrivial intersection with the path
component $S_n$, it must be contained in $S_n$. It follows that
 $S_n \cap e$ is closed and open in $e$ for each $e$, so $S_n$ is closed and open in
$X_n$. Since we are assuming that $X_n$ is connected, it follows that $S_n = X_n$.

Now, assume we have shown that $X_{k-1}$ is path-connected for $k > n$, and let $S_k$
be the path component of $X_k$ containing $X_{k-1}$. For each $k$-cell $e$, its closure
is a path-connected subset of $X_k$ that has a nontrivial intersection with $X_{k-1}$,
so it is contained in $S_k$. It follows that $X_k = S_k$, and the induction is
complete. $\square$

Next we address the question of compactness, which is similarly easy to detect in CW
complexes. First we establish two simple preliminary results.

**Lemma 5.12.** In any CW complex, the closure of each cell is contained in a finite
subcomplex.

*Proof.* Let $X$ be a CW complex, and let $e'$ be an $n$-cell; we prove the lemma by
induction on $n$. If $n = 0$, then $e'$ is itself a finite subcomplex, so assume the
lemma is true for every cell of dimension less than $n$. Then by condition (C), $e'$
is contained in the union of finitely many cells of lower dimension, each of which is
contained in a finite subcomplex by the inductive hypothesis. The union of these
finite subcomplexes together with $e'$ is a finite subcomplex containing $e'$. $\square$

**Lemma 5.13.** Let $X$ be a CW complex. A subset of $X$ is discrete if and only if its
intersection with each cell is finite.

*Proof.* Suppose $S \subset X$ is discrete. For each cell $e$ of $X$, the intersection
$S \cap e$ is a discrete subset of the compact set $e$, so it is finite, and thus so
also is $S \cap e$. Conversely, suppose $S$ is a subset whose intersection with each
finite subcomplex is finite; because the closure of each cell is contained in a finite
subcomplex, the hypothesis implies that $S \cap e$ is finite for each $e$. This means
that $S \cap e$ is closed in $e$, and thus by condition (W), $S$ is closed in $X$. But
the same argument applies to every subset of $S$; thus every subset of $S$ is closed
in $X$, which implies that the subspace topology on $S$ is discrete. $\square$

**Theorem 5.14.** Let $X$ be a CW complex. A subset of $X$ is compact if and only if it
is closed in $X$ and contained in a finite subcomplex.

*Proof.* Every finite subcomplex $Y \subset X$ is compact, because it is the union of
finitely many compact sets of the form $\overline{e}$. Thus if $K \subset X$ is closed
and contained in a finite subcomplex, it is also compact. Conversely, suppose $K \subset
X$ is compact. If $K$ intersects infinitely many cells, by choosing one point of $K$ in
each such cell we obtain an infinite discrete subset of $K$, which is impossible.
Therefore, $K$ is contained in the union of finitely many cells, and thus in a finite
subcomplex by Lemma 5.12. $\square$

**Corollary 5.15.** A CW complex is compact if and only if it is a finite complex.

Local compactness of CW complexes is also easy to characterize.

**Proposition 5.16.** A CW complex is locally compact if and only if it is locally
finite.

*Proof.* Proposition 5.11. $\square$

# Inductive Construction of CW Complexes

Now we are almost ready to describe how to construct CW complexes by attaching cells
of successively higher dimensions, as promised. First we have the following lemma.

**Lemma 5.17.** Suppose $X$ is a CW complex, $\{ e_\alpha \}$ is the collection of
cells of $X$, and for each $\alpha$, $\varphi_\alpha : D_\alpha^n \to X$ is a
characteristic map for the cell $e_\alpha$. Then the map $\bigsqcup_\alpha D_\alpha^n
\to X$ whose restriction to each $D_\alpha$ is $\varphi_\alpha$ is a quotient map.

*Proof.* The map $\varphi_\alpha$ can be expressed as the composition of two maps. The
map $\varphi_\alpha : D_\alpha \to X$ is a quotient map by the closed map lemma and
Proposition 3.62(c), and the map $\bigsqcup_\alpha D_\alpha \to X$ induced by inclusion
of each set is the quotient map of Lemma 5.2.1(b). Thus their composition is a
quotient map. $\square$

**Proposition 5.18.** Let $X$ be a CW complex. Each skeleton $X_n$ is obtained from
$X_{n-1}$ by attaching a collection of $n$-cells.

*Proof.* Let $\{ e_\alpha \}$ be the collection of $n$-cells of $X$, and for each
$n$-cell $e_\alpha$, let $\varphi_\alpha : D_\alpha^n \to X$ be a characteristic map.
Define $\varphi : \bigsqcup_\alpha D_\alpha^n \to X$ to be the map whose restriction to
each $D_\alpha^n$ is the restriction of $\varphi_\alpha$. By definition of a cell
complex, $\varphi$ takes its values in $X_n$, so we can form the adjunction space
$X_{n-1} \cup_\varphi \left(\bigsqcup D_\alpha^n\right)$.

The map $\varphi : \left(\bigsqcup D_\alpha^n\right) \to X_n$ that is equal to the
inclusion on $X_{n-1}$ and to $\varphi_\alpha$ on each $D_\alpha^n$ makes the same
identifications as the quotient map defining the adjunction space, so in fact $X_n$ is
homeomorphic to the adjunction space shown in the preceding paragraph.

Let $A \subset \bigsqcup D_\alpha^n$ be a saturated closed subset of the disjoint
union, and let $B = \varphi(A)$, so that $A = \varphi^{-1}(B)$. The hypothesis means
that $A \cap D_\alpha^n$ is closed in $D_\alpha^n$ for each $\alpha$. The first
assertion implies that $B \cap e$ is closed in $e$ for every cell $e$ of dimension
less than $n$; and the second implies that $B \cap e$ is closed in $e$ for each
$n$-cell $e$ because $\varphi_\alpha : D_\alpha^n \to e$ is a closed map by the closed
map lemma. Thus $B$ is closed in $X_n$. It follows from Proposition 3.62 that
$\varphi$ is a quotient map. $\square$

*Exercise 5.19.* Suppose $X$ is an $n$-dimensional CW complex with $n \ge 1$, and $e$ is
any $n$-cell of $X$. Show that $X - e$ is a subcomplex, and $X$ is homeomorphic to an
adjunction space obtained from $X - e$ by attaching a single $n$-cell.

The next theorem, which is a sort of converse to Proposition 5.18, shows how to
construct CW complexes by inductively attaching cells.

**Theorem 5.20 (CW Construction Theorem).** Suppose $X_0 \subset X_1 \subset \cdots
\subset X_n \subset \cdots$ is a sequence of topological spaces satisfying the
following conditions:

(1) $X_0$ is a nonempty discrete space.

(2) For each $n \ge 1$, $X_n$ is obtained from $X_{n-1}$ by attaching a (possibly
empty) collection of $n$-cells.

Then $X = \bigcup_n X_n$ has a unique topology coherent with the family $\{X_n\}$, and
a unique cell decomposition making it into a CW complex whose $n$-skeleton is $X_n$ for
each $n$.

*Proof.* Give $X$ a topology by declaring a subset $B \subset X$ to be closed if and
only if $B \cap X_n$ is closed in $X_n$ for each $n$. It is immediate that this is a
topology, and it is obviously the unique topology coherent with $\{X_n\}$. Within this
topology, each $X_n$ is a subspace of $X$; if $B$ is closed in $X$ then $B \cap X_n$ is
closed in $X_n$ by definition of the topology of $X$; conversely, if $B$ is closed in
$X$, then by virtue of the fact that each $X_{n-1}$ is closed in $X_n$ by Proposition
3.77, it follows that $B \cap X_m$ is closed in $X_m$ for all $m$, and thus $B$ is
closed in $X$.

Next we define the cell decomposition of $X$. The $0$-cells are just the points of the
discrete space $X_0$. For each $n \ge 1$, let

$$
q_n : X_{n-1} \sqcup \left(\bigsqcup_{\alpha \in A_n} D_\alpha^n\right) \to X_n
$$

be a quotient map realizing $X_n$ as an adjunction space. Proposition 3.77 shows that
$X_{n-1}$ is an open subset of $X_n$ homeomorphic to $X_{n-1}$. Since
$X_n - X_{n-1}$ is an open subset of $X_n$ homeomorphic to $\bigsqcup \operatorname{Int}
D_\alpha^n$, which is a disjoint union of open $n$-cells, we can define the $n$-cells
of $X$ to be the components $e_\alpha^n$ of $X_n - X_{n-1}$. These are subspaces of
$X_n$, and hence of $X$, and $X$ is the disjoint union of all its cells.

For each $n$-cell $e_\alpha^n$, define a characteristic map $\varphi_\alpha^n : D_\alpha^n
\to X$ as the composition

$$
D_\alpha^n \to X_{n-1} \sqcup \left(\bigsqcup_{\alpha \in A_n} D_\alpha^n\right) \xrightarrow{q_n} X_n \hookrightarrow X.
$$

Clearly $\varphi_\alpha^n$ maps $\partial D_\alpha^n$ into $X_{n-1}$, and its
restriction to $\operatorname{Int} D_\alpha^n$ is a bijective continuous map onto
$e_\alpha^n$, so we need only show that this restriction is a homeomorphism onto its
image. This follows because $q_n|_{D_\alpha^n}$ is a quotient on $\operatorname{Int}
D_\alpha^n$, so the restriction to the saturated open subset $\operatorname{Int}
D_\alpha^n$ is a bijective quotient map onto $e_\alpha^n$. This proves that $X$ has a
cell decomposition for which $X_n$ is the $n$-skeleton for each $n$. Because the
$n$-cells of this decomposition are the components of $X_n - X_{n-1}$, this is the
disjoint union of all open cells.

Next we show that $X$ is Hausdorff. By Exercise 2.35, it suffices to show that for
each $p \in X$, there exists a continuous function $f : X \to [0,1]$ such that
$f^{-1}(0) = \{ p \}$. To prove the existence of such an $f$, let $p \in X$ be
arbitrary, and let $e^n$ be the unique cell containing $p$, with $n = \dim e^n$. Let
$\varphi : D_\alpha^n \to X$ be the corresponding characteristic map. We start by
defining a map $f_n : D_\alpha^n \to [0,1]$ as follows. If $n = 0$, just let
$f_n(p) = 0$ and $f_n(x) = 1$ for $x \ne p$. Otherwise, let $\hat{p} = \varphi^{-1}(p)
\in \operatorname{Int} D_\alpha^n$. By the result of Problem 5-2(c), there is a
continuous function $f : D_\alpha^n \to [0,1]$ that is equal to $1$ on $\partial
D_\alpha^n$ and is equal to $0$ exactly at $\hat{p}$. Define $f_n : X_n \to [0,1]$ by

$$
f_n =
\begin{cases}
f \circ \varphi^{-1} & \text{on } e^n, \\
1 & \text{everywhere else}.
\end{cases}
$$

Then $f_n$ is continuous by the characteristic property of the disjoint union, and
descends to the quotient to yield a continuous function $\overline{f}_n : X_n \to
[0,1]$ whose zero set is $\{ p \}$.

Now suppose $p \in X_n$ and for some $m > n$ we have defined a continuous function
$\overline{f}_m : X_m \to [0,1]$ whose zero set is $\{ p \}$. Define a map
$f_{m+1} : X_{m+1} \to [0,1]$ by letting $f_{m+1} = \overline{f}_m$ on $X_m$. For each
$n$-cell $e_\alpha^n$, the function $\overline{f}_m \circ \varphi_\alpha :
\partial D_\alpha^{m+1} \to [0,1]$ extends to a continuous function
$\overline{f}_{m+1,\alpha} : D_\alpha^{m+1} \to [0,1]$ that has no zeros in
$\operatorname{Int} D_\alpha^{m+1}$. Define $f_{m+1}$ on each $D_\alpha^{m+1}$ by letting

$$
f_{m+1} = \overline{f}_{m+1,\alpha} \circ \varphi_\alpha^{-1}.
$$

As before, $f_{m+1}$ is continuous and descends to the quotient to yield a function
$\overline{f}_{m+1} : X_{m+1} \to [0,1]$ whose zero set is $\{ p \}$.

Finally, we just define $f : X \to [0,1]$ by letting $f(x) = \overline{f}_n(x)$ if
$x \in X_n$. This function is continuous by Proposition 5.2.2. This completes the
proof that $X$ is Hausdorff, so it is a cell complex by Proposition 5.2.2.

To show that $X$ satisfies conditions (C) and (W), first we prove by induction on $n$
that $X_n$ satisfies conditions (C) and (W). The case $n = 0$ is clear; $X_0$ is a
discrete space. Suppose they hold for $X_{n-1}$, so that $X_{n-1}$ is a CW complex. To
prove condition (C), just note that for any $n$-cell $e \subset X_n$, the closure
$\overline{e}$ is contained in a finite subcomplex of $X_{n-1}$. To prove condition
(W), suppose $B \subset X_n$ is closed in each $e$; by (W) on $X_{n-1}$ it follows that
$B \cap X_{n-1}$ is closed in $X_{n-1}$. It remains to show that $B$ is closed in $X_n$.
Let $q_n : X_{n-1} \sqcup \left(\bigsqcup D_\alpha^n\right) \to X_n$ be the quotient map
defining the adjunction space. Since $B \cap X_{n-1}$ is closed in $X_{n-1}$ and
$B \cap D_\alpha^n$ is closed in $D_\alpha^n$ for each $\alpha$, it follows that
$q_n^{-1}(B)$ is closed in $X_{n-1} \sqcup \left(\bigsqcup D_\alpha^n\right)$, so $B$ is
closed in $X_n$ by definition of the quotient topology. It follows from the argument
in the preceding paragraph (because the closure of each cell lies in some $X_n$) that
$B$ is closed in $X$ by definition of the topology of $X$.

Here is an interesting example of a CW complex constructed in this way.

**Example 5.21.** In Example 5.8(d), we showed how to obtain $S^n$ from $S^{n-1}$ by
attaching two $n$-cells. Continuing this process by induction, we obtain an infinite-
dimensional CW complex $S^\infty = \bigcup_n S^n$, with two cells in every dimension.
It contains every sphere $S^n$ as a subcomplex.

The inductive description of CW complexes is often useful in defining maps out of CW
complexes inductively cell by cell. One example of such a construction was the
construction of the function $f$ in the proof of Theorem 5.20 used to show that $X$ is
Hausdorff. The proof of the next theorem uses another example of this technique.

**Theorem 5.22.** Every CW complex is paracompact.

*Proof.* Suppose $X$ is a CW complex, and $\mathcal{U} = (U_\alpha)_{\alpha \in A}$ is
an indexed open cover of $X$. We will show that there is a partition of unity
$(\varphi_\alpha)_{\alpha \in A}$ subordinate to $\mathcal{U}$; it then follows from
Problem 4-33 that $X$ is paracompact.

For each nonnegative integer $n$, let $U_\alpha^n = U_\alpha \cap X_n$. We begin by
constructing by induction, for each $n$, a partition of unity $(\psi_\alpha^n)$ for
$X_n$ subordinate to $(U_\alpha^n)$.

For $n = 0$, we simply choose for each $x \in X_0$ a set $U_\alpha$ such that $x \in
U_\alpha$, and let $\psi_\alpha^0(x) = 1$ and $\psi_\beta^0(x) = 0$ for $\beta \ne
\alpha$.

Now suppose that for $n = 0, \ldots, k$, we have defined partitions of unity
$(\psi_\alpha^n)$ for $X_n$ subordinate to $(U_\alpha^n)$, satisfying the following
properties for each $\alpha \in A$ and each $k$:

(i) $\psi_\alpha^k|_{X_{k-1}} = \psi_\alpha^{k-1}$.

(ii) If $V_\alpha^{k-1} = \psi_\alpha^{k-1}{}^{-1}(0)$ is an open subset of $X_{k-1}$,
then there is an open subset $V' \subset X_k$ containing $V_\alpha^{k-1}$ on which
$\psi_\alpha^k = 0$.

Let $q_k : X_{k-1} \sqcup \left(\bigsqcup D_\alpha^k\right) \to X_k$ be a quotient map
realizing $X_k$ as an adjunction space. We will extend each function
$\psi_\alpha^{k-1}$ to $\psi_\alpha^k$ on $X_k$ by cell.

For each $k$-cell $e_\beta$, let $\varphi_\beta : D_\beta^k \to X_k$ be the
characteristic map. For each $\alpha$, let
$\tilde{\psi}_\alpha = \psi_\alpha^{k-1} \circ \varphi_\beta|_{\partial D_\beta^k}$ and
let $f_\beta : \partial D_\beta^k \to X_{k-1}$ be the corresponding attaching map. For
any subset $A \subset \partial D_\beta^k$ and $0 < \varepsilon < 1$, let
$A(\varepsilon) \subset D_\beta^k$ be the subset

$$
A(\varepsilon) = \{ x \in D_\beta^k : d(x, A) < \varepsilon \text{ and } 1 - \varepsilon
< |x| \le 1 \},
$$

where the norm $|x|$ is defined with respect to some homeomorphism of $D_\beta^k$ with
$B^k$. In particular, $\partial D_\beta^k$ is the set of all $x \in D_\beta^k$ such
that $|x| = 1$.

By compactness of the set $\partial D_\beta^k$ and local finiteness of the indexed
cover $(U_\alpha^k)$, there are only finitely many indices $\alpha_1, \ldots, \alpha_r$
for which $\tilde{\psi}_{\alpha_i}$ is not identically zero on $\partial D_\beta^k$.
For each such index, $A_i = \operatorname{supp} \tilde{\psi}_{\alpha_i}$ is a compact
subset of $\partial D_\beta^k$, so there is some $\varepsilon_i \in (0,1)$ such that
$A_i(\varepsilon_i) \subset \varphi_\beta^{-1}(U_{\alpha_i}^k)$. Let
$\sigma : D_\beta^k \to [0,1]$ be a continuous function that is equal to $1$ on
$\bigcup_i A_i(\varepsilon_i/2)$ and supported in $\bigcup_i A_i(\varepsilon_i)$.
Define

$$
\tilde{\psi}_{\alpha_i}'(x) = \sigma(x)\tilde{\psi}_{\alpha_i}(x) +
(1-\sigma(x))\tilde{\psi}_{\alpha_i}\!\left(\frac{x}{|x|}\right)
$$

for $x \in D_\beta^k$. Then $\tilde{\psi}_{\alpha_i}'$ is continuous and supported in
$\varphi_\beta^{-1}(U_{\alpha_i}^k)$, and the restriction of $\tilde{\psi}_{\alpha_i}'$
to $\partial D_\beta^k$ is equal to $\tilde{\psi}_{\alpha_i}$. A computation shows that
$\sum \tilde{\psi}_{\alpha_i}' = 1$ on $\partial D_\beta^k$. By construction,
$\tilde{\psi}_{\alpha_i}'$ is supported in $\varphi_\beta^{-1}(U_{\alpha_i}^k)$ and
satisfies (i).

To check that (ii) is also satisfied, suppose $V \subset X_{k-1}$ is an open subset on
which $\psi_\alpha^{k-1} = 0$. Then for each $y$, there is an open subset $V_y$ of
$\partial D_\beta^k$ on which $\tilde{\psi}_\alpha = \psi_\alpha^{k-1} \circ f_\beta$ is
zero. The union of $V$ together with the images of these sets is an open subset of
$X_k$ on which $\psi_\alpha^k = 0$. To show that the indexed cover
$(\psi_\alpha^{k+1})$ is locally finite, note that $X_{k+1} = X_k \cup \bigcup e_\alpha^{k+1}$,
and thus that the interior of an $(n+1)$-cell; then for each point $x$ in $X_{k+1}$,
there is a neighborhood $V$ of $x$ in which only finitely many of the functions
$\psi_\alpha^{k+1}$ are nonzero by construction. On the other hand, if $x \in X_k$,
because $(\psi_\alpha^k)$ is locally finite, there is a neighborhood $V$ of $x$ in
$X_k$ on which $\psi_\alpha^k = 0$ except when $\alpha$ is one of finitely many
indices. This implies that if $x \in X_k$, we may choose a neighborhood $V$ in
$X_{k+1}$ such that $\psi_\alpha^{k+1} = 0$ on $V$ for all but finitely many indices.
This completes the induction.

Finally, for each $\alpha$, define $\psi_\alpha : X \to [0,1]$ to be the function whose
restriction to each $X_n$ is $\psi_\alpha^n$. This is well defined, and because the
topology of $X$ is coherent with its $n$-skeleton, it is continuous. Because
$\sum \psi_\alpha = 1$ for each $n$, it follows that $\sum \psi_\alpha = 1$ on $X$. To
prove local finiteness, note that if $x \in X_n$ for some $n$, and because
$(\psi_\alpha^n)$ is locally finite, there is a neighborhood $V$ of $x$ in $X_n$ on
which $\psi_\alpha^n = 0$ except for finitely many choices of $\alpha$. Then $V$ is an
open neighborhood of $x$ in $X$ on which all but finitely many of the functions
$\psi_\alpha$ are identically zero. Thus $(\psi_\alpha)$ is the required partition of
unity. $\square$
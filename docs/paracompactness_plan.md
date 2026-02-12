# Plan for Proving `instCWComplexParacompactSpace`

Based on Theorem 5.22 from the textbook: *Every CW complex is paracompact.*

The proof uses the already-available helper `paracompact_of_exist_partition_of_unity`: it suffices to construct, for every indexed open cover, a subordinate partition of unity. This is done by induction on skeleta, then gluing via coherence.

---

## 1. Additional Definitions Required

### Definition A: `CompatibleSkeletonPOU`

The inductive data at each stage — a partition of unity on the n-skeleton, subordinate to the restricted cover.

```lean
structure CompatibleSkeletonPOU (α : Type*) (s : α → Set X) (n : ℕ) where
  toFun : α → C(Skeleton X n, ℝ)
  nonneg : ∀ a (x : Skeleton X n), 0 ≤ toFun a x
  sum_eq_one : ∀ x : Skeleton X n, ∑ᶠ a, toFun a x = 1
  locallyFinite : LocallyFinite (fun a => Function.support (toFun a))
  subordinate : ∀ a, tsupport (toFun a) ⊆ (Subtype.val ⁻¹' (s a))
```

Compatibility between levels is captured by a separate statement (Lemma 6 below), since in Lean the types of the functions change as `n` varies.

### Definition B: `radialProjection`

Radial retraction from the closed ball (minus center) to the sphere.

```lean
noncomputable def radialProjection (n : ℕ) (x : cb n) (hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≠ 0) : sph n
```

This is the map `x ↦ x/|x|` used in the interpolation formula `ψ̃'(x) = σ(x)·ψ̃(x) + (1-σ(x))·ψ̃(x/|x|)`.

### Definition C: `thickenedBoundaryNhd`

The set A(ε) from the textbook.

```lean
def thickenedBoundaryNhd (n : ℕ) (A : Set (sph n)) (ε : ℝ) : Set (cb n)
```

For `A ⊆ ∂D^k` and `0 < ε < 1`, this is the set `{x ∈ D^k | d(x,A) < ε ∧ 1-ε < ‖x‖ ≤ 1}` — a neighborhood of `A` in the disk that retracts onto `A`, used to define the bump function `σ`.

---

## 2. Lemmas Required

### Lemma 1: Base case — POU on the 0-skeleton

```lean
lemma skeleton_pou_zero
    (s : α → Set X) (hs_open : ∀ a, IsOpen (s a)) (hs_cover : ⋃ a, s a = Set.univ) :
    CompatibleSkeletonPOU α s 0
```

**Proof idea:** `Skeleton X 0` has `DiscreteTopology` (from `skeleton0_discrete`). For each point `x ∈ X_0`, pick some `α` with `x ∈ U_α`, set `ψ_α^0(x) = 1` and all others to 0. Everything is automatically continuous on a discrete space. Local finiteness is trivial since each point has a singleton neighborhood.

### Lemma 2: Finitely many nonzero pullbacks on cell boundary

```lean
lemma finitely_nonzero_on_cell_boundary (n : ℕ)
    (pou : CompatibleSkeletonPOU α s n)
    (e : CellOfDim (n + 1)) :
    {a : α | ¬ ∀ x : sph (n + 1), pou.toFun a (attach_map e x) = 0}.Finite
```

where `attach_map e` is the composition of the attaching map with the inclusion `Skeleton X n → Skeleton X (n+1)`.

**Proof idea:** The pullback of each `ψ_α^n` to `∂D^{n+1}` is continuous. By compactness of `sph (n+1)` and local finiteness of the POU, only finitely many are nonzero.

### Lemma 3: Extension of a single function from boundary to disk

```lean
lemma extend_boundary_to_disk (n : ℕ)
    (f : C(sph (n + 1), ℝ)) (hf_nonneg : ∀ x, 0 ≤ f x)
    (U : Set (cb (n + 1))) (hU_open : IsOpen U)
    (hf_supp : tsupport f ⊆ sph_to_cb ⁻¹' U) :
    ∃ g : C(cb (n + 1), ℝ),
      (∀ x : sph (n + 1), g (sph_to_cb x) = f x) ∧
      (∀ x, 0 ≤ g x) ∧
      (tsupport g ⊆ U)
```

**Proof idea:** Uses the interpolation formula from the textbook:

$$g(x) = \sigma(x) \cdot \tilde{f}(x) + (1 - \sigma(x)) \cdot \tilde{f}(x/|x|)$$

where `σ` is a bump function (from Urysohn's lemma, already imported via `Mathlib.Topology.UrysohnsLemma`) and `f̃` is the pullback of `f` via radial projection. The bump function `σ` is 1 near the support of `f̃` and supported inside `U`. Continuity of the radial projection at the boundary (where `|x|=1`) makes the whole thing continuous.

### Lemma 4: Extension sum is still 1 on boundary

```lean
lemma extend_sum_eq_one_on_boundary (n : ℕ)
    (fs : Fin r → C(sph (n + 1), ℝ))
    (gs : Fin r → C(cb (n + 1), ℝ))
    (h_extend : ∀ i x, gs i (sph_to_cb x) = fs i x)
    (h_sum : ∀ x, ∑ i, fs i x = 1) :
    ∀ x : sph (n + 1), ∑ i, gs i (sph_to_cb x) = 1
```

Essentially immediate from `h_extend` and `h_sum`.

### Lemma 5: Extension sum is 1 everywhere on the disk

```lean
lemma extend_sum_eq_one_on_disk (n : ℕ)
    (pou : CompatibleSkeletonPOU α s n)
    (e : CellOfDim (n + 1))
    (gs : α → C(cb (n + 1), ℝ))
    (h_extend : ∀ a (x : sph (n+1)), gs a (sph_to_cb x) = pou.toFun a (attach_map e x))
    (h_finsupp : {a : α | ¬ ∀ x, gs a x = 0}.Finite) :
    ∀ x : cb (n + 1), ∑ᶠ a, gs a x = 1
```

**Proof idea:** By the interpolation formula, for any `x ∈ D^{n+1}`:

$$\sum g_\alpha(x) = \sigma(x) \cdot \sum \tilde{\psi}_\alpha(x) + (1-\sigma(x)) \cdot \sum \tilde{\psi}_\alpha(x/|x|) = \sigma(x) \cdot 1 + (1-\sigma(x)) \cdot 1 = 1$$

using that the original functions summed to 1 on the boundary.

### Lemma 6: Inductive step — extend POU from skeleton n to skeleton n+1

```lean
lemma skeleton_pou_succ (n : ℕ)
    (s : α → Set X) (hs_open : ∀ a, IsOpen (s a)) (hs_cover : ⋃ a, s a = Set.univ)
    (pou_n : CompatibleSkeletonPOU α s n) :
    ∃ pou : CompatibleSkeletonPOU α s (n + 1),
      ∀ a (x : Skeleton X n),
        pou.toFun a ⟨x.1, skeleton_mono n (n+1) (Nat.le_succ n) x.2⟩ = pou_n.toFun a x
```

**Proof idea:** Combine Lemmas 2–5. For each (n+1)-cell, extend the pullback of `pou_n` from the boundary to the disk. The resulting functions on `X_{n+1}` are continuous because `X_{n+1}` has the quotient topology from `X_n ⊔ ⊔_β D^{n+1}` (from `skn_sum_cnp1_to_sknp1` and the adjunction space construction). The compatibility condition is built into the extension (it equals the old value on the boundary, which is identified with `X_n`).

### Lemma 7: Glue skeletal POUs into a global POU using coherence

```lean
lemma glue_skeleton_pous
    (s : α → Set X) (hs_open : ∀ a, IsOpen (s a)) (hs_cover : ⋃ a, s a = Set.univ)
    (pou : ∀ n, CompatibleSkeletonPOU α s n)
    (compat : ∀ n a (x : Skeleton X n),
      (pou (n+1)).toFun a ⟨x.1, skeleton_mono n (n+1) (Nat.le_succ n) x.2⟩ =
      (pou n).toFun a x) :
    ∃ p : PartitionOfUnity α X, p.IsSubordinate s
```

**Proof idea:**

- **Well-definedness:** For each `α`, define `ψ_α(x) = (pou n).toFun α ⟨x, hx⟩` for any `n` with `x ∈ Skeleton X n`. Compatibility ensures this is independent of the choice of `n`.
- **Continuity:** By `CW.coeherent` (coherence), a function on `X` is continuous iff its restriction to each cell closure is continuous (`continuous_of_coherent`). On each cell closure `cl(e)`, the function factors through the characteristic map `φ_e : cb(dim e) → X`, and the composition is continuous because it equals the skeletal POU restricted to a compact set.
- **Sum = 1:** Holds on each skeleton by construction, hence on all of X.
- **Local finiteness:** For `x ∈ X_n`, local finiteness of `(pou n)` gives a neighborhood in `X_n` where all but finitely many are zero. By coherence, this lifts to a neighborhood in X.
- **Subordination:** `tsupport(ψ_α) ⊆ U_α` follows from the skeletal subordination.

---

## 3. Proof Skeleton for `instCWComplexParacompactSpace`

```lean
instance instCWComplexParacompactSpace : ParacompactSpace X := by
  apply paracompact_of_exist_partition_of_unity
  intro α s hs_open hs_cover
  -- Step 1: Build compatible POUs on each skeleton by induction
  have pou_family : ∀ n, ∃ (pou : CompatibleSkeletonPOU α s n),
      ∀ (m : ℕ) (hm : m < n) (a : α) (x : Skeleton X m),
        pou.toFun a ⟨x.1, skeleton_mono m n (Nat.le_of_lt_succ (by linarith)) x.2⟩ =
        sorry /- value from lower POU -/ := by
    intro n
    induction n with
    | zero =>
      exact ⟨skeleton_pou_zero s hs_open hs_cover, by intro m hm; omega⟩
    | succ k ih =>
      obtain ⟨pou_k, hpou_k⟩ := ih
      obtain ⟨pou_succ, hcompat⟩ := skeleton_pou_succ k s hs_open hs_cover pou_k
      exact ⟨pou_succ, sorry /- extend compatibility -/⟩
  -- Step 2: Extract a compatible system
  choose pou_n hpou_n using pou_family
  -- Step 3: Glue into a global POU using coherence
  exact glue_skeleton_pous s hs_open hs_cover pou_n sorry
```

---

## Dependency Graph

```
instCWComplexParacompactSpace
  ├── paracompact_of_exist_partition_of_unity  [already proved]
  ├── skeleton_pou_zero                        [Lemma 1]
  │     └── skeleton0_discrete                 [already proved]
  ├── skeleton_pou_succ                        [Lemma 6]
  │     ├── finitely_nonzero_on_cell_boundary  [Lemma 2]
  │     ├── extend_boundary_to_disk            [Lemma 3]
  │     │     ├── radialProjection             [Definition B]
  │     │     ├── thickenedBoundaryNhd         [Definition C]
  │     │     └── Urysohn's lemma              [from Mathlib import]
  │     ├── extend_sum_eq_one_on_boundary      [Lemma 4]
  │     └── extend_sum_eq_one_on_disk          [Lemma 5]
  └── glue_skeleton_pous                       [Lemma 7]
        ├── continuous_of_coherent             [already proved]
        ├── skeleton_cover                     [already proved]
        └── skeleton_mono                      [already proved]
```

## Difficulty Assessment

| Component | Difficulty | Notes |
|-----------|-----------|-------|
| Lemma 1 (base case) | Easy | Discrete topology makes everything trivial |
| Lemma 2 (finite nonzero) | Medium | Compactness + local finiteness argument |
| Lemma 3 (boundary→disk extension) | Hard | Interpolation formula, radial projection continuity, Urysohn |
| Lemma 4 (sum=1 on boundary) | Easy | Direct from extension property |
| Lemma 5 (sum=1 on disk) | Medium | Follows from interpolation formula structure |
| Lemma 6 (inductive step) | Hard | Assembles cell-by-cell extensions, quotient topology |
| Lemma 7 (gluing) | Medium | Coherence argument, finitary support transfer |
| Definition A | Easy | Structure packaging |
| Definition B | Medium | Needs continuity proof for radial projection |
| Definition C | Medium | Metric geometry on the disk |

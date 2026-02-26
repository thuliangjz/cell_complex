# Plan to finish `instCWComplexParacompactSpace`

Goal in `STCC/Paracompactness.lean`:

```lean
instance instCWComplexParacompactSpace : ParacompactSpace X := by
  apply paracompact_of_exist_partition_of_unity
  intro α s hs_open hs_cover
  -- build `∃ p : PartitionOfUnity α X, p.IsSubordinate s`
```

You already have the two key ingredients:

- `skeleton_pou_zero`
- `skeleton_pou_succ`

So the remaining proof is "globalization from skeleta to `X`".

---

## Step 1 (about 50 lines): build an infinite tower of skeleton POUs

**Target type**

```lean
have h_exists_tower :
    ∃ pou : ℕ → CompatibleSkeletonPOU α s,
      (∀ n a (x : Skeleton X n),
        (pou (n + 1)).toFun a
          ⟨x.1, skeleton_mono n (n + 1) (Nat.le_add_right n 1) x.2⟩
          = (pou n).toFun a x) ∧
      (∀ n V : Set (Skeleton X n), IsOpen V →
        ∃ V' : Set (Skeleton X (n + 1)), IsOpen V' ∧
          (∀ x : Skeleton X n, x ∈ V →
            (⟨x.1, skeleton_mono n (n + 1) (Nat.le_add_right n 1) x.2⟩ :
              Skeleton X (n + 1)) ∈ V') ∧
          (∀ a, (∀ x ∈ V, (pou n).toFun a x = 0) →
            (∀ y ∈ V', (pou (n + 1)).toFun a y = 0)))
```

**How**

- Start from `pou 0 := skeleton_pou_zero s hs_open hs_cover`.
- For each `n`, apply `skeleton_pou_succ s hs_open hs_cover n (pou n)`.
- Use `Classical.choose`/`choose` to extract:
  - successor POU `pou (n+1)`,
  - restriction compatibility,
  - zero-extension compatibility.
- Package all extracted data into one tower statement.

---

## Step 2 (about 50 lines): derive restriction along arbitrary `m ≤ n`

**Target type**

```lean
have h_restrict_le :
    ∀ {m n : ℕ} (hmn : m ≤ n) (a : α) (x : Skeleton X m),
      (pou n).toFun a
        ⟨x.1, skeleton_mono m n hmn x.2⟩
        = (pou m).toFun a x
```

**How**

- Prove by induction on `hmn`.
- Base `m = n`: `simp`.
- Step `m ≤ n -> m ≤ n+1`: rewrite via
  - one-step compatibility from Step 1 at level `n`,
  - induction hypothesis at level `n`.
- This lemma is used repeatedly to eliminate dependence on skeleton level.

---

## Step 3 (about 50 lines): define global functions `ψ a : X → ℝ` and level-transfer lemmas

**Target type**

```lean
noncomputable def ψ (a : α) : X → ℝ := ...

have hψ_on_skeleton :
    ∀ (n : ℕ) (a : α) (x : Skeleton X n),
      ψ a x.1 = (pou n).toFun a x
```

**How**

- Define a level selector `level : X → ℕ` using `exists_mem_of_skeleton` (via `Classical.choose`).
- Define
  ```lean
  ψ a x := (pou (level x)).toFun a ⟨x, level_mem x⟩
  ```
- Prove transfer lemma:
  if `hx : x ∈ Skeleton X n`, then `ψ a x = (pou n).toFun a ⟨x, hx⟩`,
  using Step 2 with `hmn : level x ≤ n` (from minimality/choice witness plus monotonicity).
- This lemma is the bridge from global definition to known skeleton facts.

---

## Step 4 (about 50 lines): continuity of each `ψ a`

**Target type**

```lean
have hψ_cont : ∀ a : α, Continuous (ψ a)
```

**How**

- Use `continuous_of_coherent` (from `STCC/Basic.lean`) with the coherent family
  from `CW.coeherent`.
- So it suffices to prove continuity of `(closure e).restrict (ψ a)` for each cell closure.
- For fixed cell `e`, let `d := C.dim_map e`.
  Prove `closure e ⊆ Skeleton X d` by:
  - `e ⊆ Skeleton X d` from `sub_skeleton_iff`,
  - then `cell_closure_incl`.
- On `closure e`, rewrite `ψ` by `hψ_on_skeleton` at level `d`.
  The RHS is composition of continuous maps, hence continuous.

---

## Step 5 (about 50 lines): global nonnegativity and sum-to-one

**Target type**

```lean
have hψ_nonneg : ∀ a x, 0 ≤ ψ a x
have hψ_sum : ∀ x, ∑ᶠ a, ψ a x = 1
```

**How**

- For each `x : X`, pick a skeleton level containing `x`.
- Rewrite `ψ a x` by `hψ_on_skeleton`.
- Apply corresponding `CompatibleSkeletonPOU` fields:
  - nonnegativity: `(pou n).nonneg`,
  - partition identity: `(pou n).sum_eq_one`.

---

## Step 6 (about 50 lines): global subordination to the open cover

**Target type**

```lean
have hψ_subordinate : ∀ a, tsupport (ψ a) ⊆ s a
```

**How**

- Take `x ∈ tsupport (ψ a)`.
- Choose a skeleton containing `x`, rewrite by `hψ_on_skeleton`.
- Push `tsupport` membership from `ψ a` to the chosen skeleton function
  `(pou n).toFun a` (using restriction and closure arguments on subtypes).
- Apply `(pou n).subordinate a`.
- Conclude `x ∈ s a`.

---

## Step 7 (about 50 lines): global local finiteness

**Target type**

```lean
have hψ_locallyFinite :
    LocallyFinite (fun a => Function.support (ψ a))
```

**How (core strategy from Theorem 5.22 endgame)**

- Fix `x : X`, choose `n` with `x ∈ Skeleton X n`.
- From `(pou n).locallyFinite`, get open `Vn` around `x` in `Skeleton X n`
  and finite index set `F` controlling active supports on `Vn`.
- For each `k`, use the zero-extension clause (Step 1) to build
  `V_{n+k+1}` from `V_{n+k}` while preserving "all `a ∉ F` vanish".
- Define a global neighborhood in `X` by union of the lifted `V_{n+k}`.
- Prove:
  - it is a neighborhood of `x`,
  - if `a ∉ F`, then `Function.support (ψ a)` misses this neighborhood.
- Therefore active indices near `x` are contained in finite `F`.

(This is the longest technical block; keeping it as one dedicated lemma is recommended.)

---

## Step 8 (about 40-50 lines): package into `PartitionOfUnity` and finish the instance

**Target type**

```lean
refine ⟨?pouX, ?subordinate⟩
```

with

```lean
?pouX : PartitionOfUnity α X
?subordinate : ?pouX.IsSubordinate s
```

**How**

- Define
  ```lean
  let p : PartitionOfUnity α X := {
    toFun := fun a => ⟨ψ a, hψ_cont a⟩
    nonneg := ...
    sum_eq_one := ...
    locallyFinite := hψ_locallyFinite
  }
  ```
- Prove `p.IsSubordinate s` from Step 6.
- Return `⟨p, ...⟩`, completing
  `intro α s hs_open hs_cover`.
- This closes `instCWComplexParacompactSpace`.

---

## Recommended micro-lemmas to add first

To keep each chunk near ~50 lines and avoid giant rewrites, add these helper lemmas before the final proof:

1. `tower_restrict_le` (Step 2 target).
2. `ψ_on_skeleton` (Step 3 target).
3. `ψ_cont` via coherent criterion (Step 4 target).
4. `ψ_locallyFinite` (Step 7 target).

After these, the final instance proof should be short and mostly assembly.

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

- Break Step 4 into small lemmas:
  1. For `e : C.sets`, set `d := C.dim_map e`; prove
     `closure e.1 ⊆ Skeleton X d` using
     - `e.1 ⊆ Skeleton X d` from `sub_skeleton_iff`,
     - then `(Skeleton X d).cell_closure_incl`.
  2. For fixed `e`, define the inclusion map
     `ιe : closure e.1 → Skeleton X d`, and prove `Continuous ιe`.
  3. For fixed `a e`, prove pointwise on `closure e.1`:
     `(ψ a) z.1 = (pou d).toFun a (ιe z)` using `hψ_on_skeleton`.
  4. Deduce continuity of `(closure e.1).restrict (ψ a)` by rewriting it as
     `((pou d).toFun a) ∘ ιe` and using continuity of both factors.
  5. Apply `continuous_of_coherent CW.coeherent (ψ a)`:
     it is enough to show continuity on every `b ∈ {closure s | s ∈ C.sets}`.
     Unpack `b` as `closure e.1` and use item (4).
- Conclude `hψ_cont : ∀ a : α, Continuous (ψ a)`.

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

- Use a contrapositive strategy:
  prove `h_not_tsupport : ∀ a x, x ∉ s a → x ∉ tsupport (ψ a)`,
  then conclude `hψ_subordinate`.
- Break into micro-lemmas:
  1. (`~20 lines`) For fixed `a x` with `x ∉ s a`, choose `n` and `xn : Skeleton X n`,
     and build an open neighborhood
     `Vn := (tsupport ((pou n).toFun a))ᶜ` in `Skeleton X n` with
     `xn ∈ Vn` and `∀ z ∈ Vn, (pou n).toFun a z = 0`.
  2. (`~20 lines`) Specialize `hpou_zero_extension` to fixed `a`:
     from open `V` on level `n` with pointwise zero of `(pou n).toFun a`,
     produce open `V'` on level `n+1` containing lifts and with
     `∀ y ∈ V', (pou (n+1)).toFun a y = 0`.
  3. (`~20 lines`) Iterate (2) from level `n` upward:
     construct `Vm` for all `m ≥ n` such that lifted `x` belongs to `Vm`
     and `(pou m).toFun a` vanishes on `Vm`.
  4. (`~20 lines`) Define global neighborhood
     `W := ⋃ m ≥ n, (Subtype.val '' Vm)`; prove `IsOpen W` and `x ∈ W`.
  5. (`~20 lines`) Prove `∀ y ∈ W, ψ a y = 0`:
     combine membership witness `y ∈ Vm`, level transfer via `h_restrict_le`,
     and rewrite by `hψ_on_skeleton`.
  6. (`~20 lines`) Conclude `x ∉ tsupport (ψ a)` since `W` is an open
     neighborhood of `x` disjoint from `Function.support (ψ a)`.
- Final assembly: from `h_not_tsupport`, obtain
  `hψ_subordinate : ∀ a, tsupport (ψ a) ⊆ s a`.

---

## Step 7 (about 120-160 lines): global local finiteness

**Target type**

```lean
have hψ_locallyFinite :
    LocallyFinite (fun a => Function.support (ψ a))
```

**How (split into ~20-line micro-blocks)**

1. **Seed neighborhood + finite controller (`F`)**
   - For fixed `x : X`, choose `n` and `xn : Skeleton X n`.
   - Use `(pou n).locallyFinite` at `xn` to get:
     - open `Vn : Set (Skeleton X n)`,
     - `xn ∈ Vn`,
     - finite `F := {a | (Function.support ((pou n).toFun a) ∩ Vn).Nonempty}`.
   - Derive:
     ```lean
     ∀ a, a ∉ F → ∀ z ∈ Vn, (pou n).toFun a z = 0
     ```

2. **One-step lift preserving “outside `F` = 0”**
   - Build helper:
     ```lean
     h_lift_zero_outside_F :
       ∀ m (Vm : Set (Skeleton X (n + m))),
         IsOpen Vm →
         (∀ a, a ∉ F → ∀ z ∈ Vm, (pou (n + m)).toFun a z = 0) →
         ∃ Vm' : Set (Skeleton X (n + (m + 1))), IsOpen Vm' ∧
           (∀ z : Skeleton X (n + m), z ∈ Vm ↔
             (⟨z.1, skeleton_mono (n + m) (n + (m + 1))
               (Nat.le_add_right (n + m) 1) z.2⟩ :
               Skeleton X (n + (m + 1))) ∈ Vm') ∧
           (∀ a, a ∉ F → ∀ y ∈ Vm', (pou (n + (m + 1))).toFun a y = 0)
     ```
   - This is the `h_lift_zero_neighborhood` pattern with an extra `a ∉ F` parameter.

3. **Recursive chain `Vk`**
   - Construct `Vk : ∀ k, Set (Skeleton X (n + k))` (via `Nat.rec`) with:
     - `∀ k, IsOpen (Vk k)`,
     - one-point chain through `x`,
     - compatibility
       `z ∈ Vk m ↔ lift z ∈ Vk (m+1)`,
     - `∀ k a, a ∉ F → ∀ y ∈ Vk k, (pou (n + k)).toFun a y = 0`.

4. **Global neighborhood in `X`**
   - Define:
     ```lean
     W := ⋃ k, (Subtype.val : Skeleton X (n + k) → X) '' (Vk k)
     ```
   - Prove:
     - `x ∈ W`,
     - `IsOpen W`.
   - Openness proof should reuse the `hψ_subordinate` technique:
     - preimage formula on each skeleton level,
     - `skeleton_coeherent_of_strictMono (fun t => n + t)`,
     - `open_crit`.

5. **Uniform vanishing on `W` outside `F`**
   - Prove:
     ```lean
     ∀ a, a ∉ F → ∀ y ∈ W, ψ a y = 0
     ```
   - Decompose `y ∈ W` into `(k, yk)`, rewrite by `hψ_on_skeleton`,
     then apply chain-vanishing on `Vk k`.

6. **Finite active set near `x`**
   - Show:
     ```lean
     {a : α | (Function.support (ψ a) ∩ W).Nonempty} ⊆ F
     ```
     from Step 5.
   - Conclude finiteness of this active set using `F.Finite`.
   - Return local-finiteness witness at `x` with neighborhood `W`.

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

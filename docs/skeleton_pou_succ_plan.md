# Proof Plan: `skeleton_pou_succ`

## Goal

Given a partition of unity `pou_n : CompatibleSkeletonPOU α s n` on the
n-skeleton, construct a partition of unity on the (n+1)-skeleton satisfying:

- **(i) Restriction:** the new POU restricts to `pou_n` on `Skeleton X n`.
- **(ii) Zero-extension:** for any open `V ⊆ Skeleton X n`, there is an open
  `V' ⊆ Skeleton X (n+1)` containing `V` such that whenever `pou_n.toFun a ≡ 0`
  on `V`, we have `pou_succ.toFun a ≡ 0` on `V'`. Crucially, `V'` depends only
  on `V`, not on `a`.

## Lemma statement

```lean
theorem skeleton_pou_succ
    {α : Type*} (s : α → Set X) (hs_open : ∀ a, IsOpen (s a))
    (hs_cover : ⋃ a, s a = Set.univ)
    (n : ℕ) (pou_n : CompatibleSkeletonPOU α s n) :
    ∃ pou_succ : CompatibleSkeletonPOU α s (n + 1),
      (∀ a (x : Skeleton X n),
        pou_succ.toFun a
          ⟨x.1, skeleton_mono n (n + 1) (Nat.le_add_right n 1) x.2⟩ =
          pou_n.toFun a x) ∧
      (∀ V : Set (Skeleton X n), IsOpen V →
        ∃ V' : Set (Skeleton X (n + 1)), IsOpen V' ∧
          (∀ x : Skeleton X n, x ∈ V →
            (⟨x.1, skeleton_mono n (n + 1) (Nat.le_add_right n 1) x.2⟩ :
              Skeleton X (n + 1)) ∈ V') ∧
          (∀ a, (∀ x ∈ V, pou_n.toFun a x = 0) →
            (∀ y ∈ V', pou_succ.toFun a y = 0)))
```

---

## Step 0 — Enhance `exists_cb_pou_on_cell` with collar agreement

**Target goal.** Add a fifth conjunct exporting the collar width `ε` and the
fact that on `boundary_collar (ε / 2)` (where `σ = 0`) the cell-level POU
equals the radial pullback of `pou_n`:

```
∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
  ∀ a (x : cb (n + 1)), x.1 ≠ 0 → (1 - ε / 2 : ℝ) < ‖x.1‖ →
    cb_pou a x = pou_n.toFun a
      ⟨characteristic_cn (n+1) γ (radial_proj x).1,
       char_cnp1_boundary_in_skn n γ (radial_proj x).1 (radial_proj x).2⟩
```

**Why needed.** Property (ii) requires that `cb_pou a` vanishes on a collar
whenever `pou_n.toFun a` vanishes on the corresponding boundary region. The
existing boundary-agreement conclusion covers only `∂D`, not the collar
interior.

**How (~10 lines).** The proof of `exists_cb_pou_on_cell` already constructs
`ε`, `σ`, `hσ_boundary`. On `boundary_collar (ε / 2)`, `σ x = 0`, so
`cb_pou_candidate a x = phi a x`. For `x.1 ≠ 0`,
`phi a x = boundary_pullback a (radial_proj x)` by definition. Unfolding
`boundary_pullback` gives the stated equality.

---

## Step 1 — Choose cell-level POUs for all cells

**Target goal.** For each `γ : CellOfDim (n + 1)`, obtain
`cb_pou γ : α → C(cb (n+1), ℝ)` and a collar width `cb_ε γ : ℝ` with all
five properties from the enhanced `exists_cb_pou_on_cell`.

**How (~15 lines).** Apply the enhanced `exists_cb_pou_on_cell` to each `γ`,
then use `choose` to extract:

- `cb_pou : CellOfDim (n+1) → α → C(cb (n+1), ℝ)`
- `cb_ε : CellOfDim (n+1) → ℝ`
- Five families of hypotheses: `h_nonneg`, `h_sum`, `h_sub`, `h_boundary`,
  `h_collar`.

---

## Step 2 — Define function on disjoint sum and show factoring

**Target goal.** For each `a : α`, define

```
pou_ext a : Skeleton X n ⊕ (Σ γ : CellOfDim (n+1), cb (n+1)) → ℝ
```

by `Sum.inl x ↦ pou_n.toFun a x` and `Sum.inr ⟨γ, y⟩ ↦ cb_pou γ a y`.
Then prove it factors through `glue_setoid`:

```
glue_setoid ... x₁ x₂ → pou_ext a x₁ = pou_ext a x₂
```

**How (~20 lines).** Case-split via `glue_rel_equiv_explicit`:

| Case | Why equal |
|------|----------|
| Both `Sum.inl` | `rfl` |
| `Sum.inl x` ~ `Sum.inr ⟨γ, y⟩` (boundary) | `h_boundary γ a y hy` |
| Both `Sum.inr`, same image | chain two boundary agreements |
| Reflexive | `rfl` |

---

## Step 3 — Lift to `Skeleton X (n+1)` and prove continuity

**Target goal.** Define `pou_succ_fun : α → C(Skeleton X (n+1), ℝ)`.

**How (~20 lines).**

1. `Quotient.lift (pou_ext a) (factoring)` gives a function on the
   cell-attachment quotient `CellAttached`.
2. Compose with the inverse of `cell_attached_to_sknp1_homeomorphic` to obtain
   `pou_succ_raw a : Skeleton X (n+1) → ℝ`.
3. **Continuity:** `pou_ext a` is continuous on each summand (`pou_n.toFun a`
   and `cb_pou γ a`), hence on the disjoint sum. `Quotient.lift` preserves
   continuity. Composition with the continuous inverse of a homeomorphism
   preserves continuity.
4. Package as `⟨pou_succ_raw a, ...⟩ : C(Skeleton X (n+1), ℝ)`.

---

## Step 4 — Prove nonnegativity and sum equals one

**Target goal.**

```
∀ a (x : Skeleton X (n+1)), 0 ≤ pou_succ_fun a x
∀ x : Skeleton X (n+1), ∑ᶠ a, pou_succ_fun a x = 1
```

**How (~20 lines).** For any `x`, use `skn_sum_cnp1_to_sknp1_surj` to obtain a
preimage `x'` in the disjoint sum. Then `pou_succ_fun a x = pou_ext a x'`.

- **Nonneg:** if `Sum.inl`, use `pou_n.nonneg`; if `Sum.inr ⟨γ, y⟩`, use
  `h_nonneg γ`.
- **Sum = 1:** if `Sum.inl`, use `pou_n.sum_eq_one`; if `Sum.inr ⟨γ, y⟩`, use
  `h_sum γ`.

---

## Step 5 — Prove subordination and restriction property (i)

**Target goal.**

```
∀ a, tsupport (pou_succ_fun a) ⊆ Subtype.val ⁻¹' (s a)

∀ a (x : Skeleton X n),
  pou_succ_fun a ⟨x.1, skeleton_mono ... x.2⟩ = pou_n.toFun a x
```

**How (~20 lines).**

- **Restriction (i):** for `x : Skeleton X n`, the inclusion into
  `Skeleton X (n+1)` has preimage `Sum.inl x`. So
  `pou_succ_fun a (incl x) = pou_ext a (Sum.inl x) = pou_n.toFun a x`.
- **Subordination (broken into Lean-sized sub-steps):**
  1. **Setup / goal type (`Subset` introduction, ~10-20 lines).**
     Start
     `intro a x hx`; target is `x.1 ∈ s a` from
     `hx : x ∈ tsupport (pou_succ_fun a)`.
     Immediately state a dichotomy for `x`:
     either `x` comes from embedded `Skeleton X n`, or `x` is in the interior
     of some `(n+1)`-cell.
  2. **Case A goal type (`∃ x0 : Skeleton X n, ...`, ~15-25 lines).**
     Assume `x = ⟨x0.1, skeleton_mono ... x0.2⟩`.
     Rewrite values with `pou_succ_restrict a x0` so near/at this point
     `pou_succ_fun a` is identified with `pou_n.toFun a`.
     Convert support membership to
     `x0 ∈ tsupport (pou_n.toFun a)`, then finish by
     `exact pou_n.subordinate a ...`.
  3. **Case B goal type (`∃ γ y, interior-point representation`, ~15-25 lines).**
     Assume `x` lies in interior of a specific `(n+1)`-cell `γ`, represented by
     some `y : cb (n+1)` in that interior chart.
     Use the cell-side identification of `pou_succ_fun` with `cb_pou γ a`
     at that point to transport `hx` to
     `hy : y ∈ tsupport (cb_pou γ a)`.
  4. **Case B closure goal type (direct membership, ~5-15 lines).**
     Apply `h_cb_sub γ a hy` to get
     `characteristic_cn (n+1) γ y ∈ s a`, then rewrite this point as `x.1`
     via the interior representation. Conclude `x.1 ∈ s a`.
  5. **Finish (`by_cases`/`rcases` close, ~5-10 lines).**
     Close both branches and return the required inclusion.

---

## Step 6 — Prove zero-extension property (ii)

**Target goal.** For any open `V ⊆ Skeleton X n`, construct an open
`V' ⊆ Skeleton X (n+1)` containing `V` such that whenever
`pou_n.toFun a = 0` on `V`, then `pou_succ_fun a = 0` on `V'`.

**How (~20 lines).**

1. **Preimage of `V'` in the disjoint sum.** Left summand: `V`. Right summand
   for cell `γ`: the collar set
   `W_γ = {x : cb (n+1) | radial_proj x ∈ φ_γ⁻¹(V) ∧ ‖x.1‖ > 1 − ε_γ/2}`.
2. **`W_γ` is open.** On `{‖x.1‖ > 1 − ε_γ/2}`, radial projection is
   continuous, and `φ_γ⁻¹(V)` is open in `cb_boundary`. So `W_γ` is the
   intersection of two open sets.
3. **Saturation.** If `Sum.inl z ∈ V` and boundary point
   `Sum.inr ⟨γ, y⟩ ∼ Sum.inl z`, then `y ∈ ∂D_γ` with `φ_γ(y) = z ∈ V`,
   so `radial_proj(y) = y ∈ φ_γ⁻¹(V)` and `‖y.1‖ = 1 > 1 − ε_γ/2`.
   The converse is analogous.
4. **`V'` is open** in `Skeleton X (n+1)` because it is the image of a
   saturated open set under the quotient map, transported by the homeomorphism.
5. **Zero property.** If `pou_n.toFun a = 0` on `V`, then on `V` itself
   `pou_ext a = 0` (left summand). On `W_γ`, by collar agreement (`h_collar γ`),
   `cb_pou γ a x = pou_n.toFun a ⟨..., proj(x)⟩ = 0` since `proj(x)` maps
   into `V`. So `pou_ext a = 0` on the full preimage, hence
   `pou_succ_fun a = 0` on `V'`.

---

## Step 7 — Prove local finiteness

**Target goal.**

```
LocallyFinite (fun a => Function.support (pou_succ_fun a))
```

**How (~20 lines).** For any `x : Skeleton X (n+1)`, two cases:

- **`x` is in the interior of cell `γ`:** do this in concrete substeps.

  1. **Choose right-summand representative (≈15 lines).**  
     **Target type:**
     `∃ γ y, x = h_homeo (Quotient.mk'' (Sum.inr ⟨γ, y⟩)) ∧ y ∉ cb_boundary`.  
     **Method:** as in Step 5, get `x'` from `Quotient.exists_rep (h_homeo.symm x)`,
     rule out `Sum.inl` by contradiction with the “old skeleton” branch, then prove
     `y ∉ cb_boundary` (the same argument used around `hy_not_bd`).

  2. **Build `V_int` and support-transfer in one lemma (≈30 lines).**  
     **Target type:**
     `∃ V_int : Set (Skeleton X (n+1)),
        IsOpen V_int ∧ x ∈ V_int ∧
        (∀ a, (Function.support (pou_succ_fun a) ∩ V_int).Nonempty →
          (Function.support (cb_pou γ a) ∩ cb_boundaryᶜ).Nonempty)`.  
     **Method:** define
     `pγ : cb (n+1) → Skeleton X (n+1) := fun w => h_homeo (Quotient.mk'' (Sum.inr ⟨γ, w⟩))`,
     set `V_int := pγ '' (cb_boundaryᶜ)`. Reuse the already-developed “`p` maps interior
     opens to opens” lemma/pattern (the `h_locally_open` block in Step 5) to get
     `IsOpen V_int`; membership of `x` follows from witness `y`. For transfer, unpack
     `z ∈ V_int` as `z = pγ w` with `w ∈ cb_boundaryᶜ`, then use
     `cb_pou γ a w = pou_succ_fun a (pγ w)` (same `hfg`-style equation as Step 5) to move
     nonvanishing from `pou_succ_fun` at `z` to `cb_pou` at `w`.

  3. **Import finite activity for fixed cell `γ` (≈5–10 lines).**  
     **Target type:**
     `{a | (Function.support (cb_pou γ a) ∩ cb_boundaryᶜ).Nonempty}.Finite`.  
     **Method:** use a previously prepared lemma for cell `γ` (recommended to be added near
     Step 1) giving finite active indices on the interior; this is the exact finiteness
     input needed here.

  4. **Conclude the neighborhood finiteness at `x` (≈10 lines).**  
     **Target type:**
     `{a | (Function.support (pou_succ_fun a) ∩ V_int).Nonempty}.Finite`.  
     **Method:** apply `Set.Finite.subset` with the transfer property from Step 2 to bound
     this set by the finite set in Step 3. Package with Step 2 as the `LocallyFinite`
     witness at `x`.

  This completes the interior-cell branch without touching the `x ∈ Skeleton X n` branch.
- **`x ∈ Skeleton X n`:** do this in concrete substeps.

  1. **Pick `x0` and local finite data on the old skeleton (≈20 lines).**  
     **Target type:**
     `∃ x0 : Skeleton X n, ∃ V : Set (Skeleton X n),
        x = ⟨x0.1, skeleton_mono n (n+1) (Nat.le_add_right n 1) x0.2⟩ ∧
        IsOpen V ∧ x0 ∈ V ∧
        {a : α | (Function.support (pou_n.toFun a) ∩ V).Nonempty}.Finite`.  
     **Method:** use `h_old` to obtain `x0`. Apply `pou_n.locallyFinite x0` to get
     `⟨t, ht_nhds, ht_fin⟩`. Extract an open `V` with `x0 ∈ V` and `V ⊆ t` from `ht_nhds`,
     then deduce finiteness on `V` by `Set.Finite.subset` from `ht_fin`.

  2. **Show zero-on-`V` outside the finite index set (≈15–20 lines).**  
     **Target type:**
     `let F := {a : α | (Function.support (pou_n.toFun a) ∩ V).Nonempty};
      ∀ a, a ∉ F → ∀ u ∈ V, pou_n.toFun a u = 0`.  
     **Method:** fix `a ∉ F`, `u ∈ V`. If `pou_n.toFun a u ≠ 0`, then
     `u ∈ Function.support (pou_n.toFun a)` and hence
     `(Function.support (pou_n.toFun a) ∩ V).Nonempty`, contradiction.

  3. **Apply Step 6 to transport zeroes to `(n+1)`-skeleton (≈20 lines).**  
     **Target type:**
     `∃ V' : Set (Skeleton X (n+1)), IsOpen V' ∧ x ∈ V' ∧
        (∀ a, a ∉ F → ∀ y ∈ V', pou_succ_fun a y = 0)`.  
     **Method:** apply `pou_succ_zero_extension V hV_open`, obtaining
     `⟨V', hV'_open, hV'_contains, hV'_zero⟩`. Use `hx0` and `x0 ∈ V` to prove `x ∈ V'`.
     For `a ∉ F`, feed Step 2's zero-on-`V` fact into `hV'_zero` to get zero-on-`V'`.

  4. **Conclude finiteness on `V'` and finish this branch (≈15 lines).**  
     **Target type:**
     `{a : α | (Function.support (pou_succ_fun a) ∩ V').Nonempty}.Finite`.  
     **Method:** prove
     `{a | (Function.support (pou_succ_fun a) ∩ V').Nonempty} ⊆ F` using Step 3:
     if `a ∉ F`, Step 3 gives `pou_succ_fun a = 0` on `V'`, contradicting nonempty
     support intersection. Then apply `Set.Finite.subset` with finiteness of `F`, and
     package `⟨V', hV'_open.mem_nhds hx_in_V', ...⟩` as the local finiteness witness.

---

## Step 8 — Assemble the result

**Target goal.** Package everything into the existential.

**How (~5 lines).**

```lean
exact ⟨⟨pou_succ_fun, nonneg_proof, sum_proof, lf_proof, sub_proof⟩,
       restriction_proof, zero_extension_proof⟩
```

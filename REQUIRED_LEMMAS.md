# Required Lemmas for Completing the Proof at Line 1942

## Context
We need to prove:
```lean
Subtype.val '' ((Function.invFun (CWC.Fφ (pid_to_nat p + m))) '' 
  ((Quotient.mk _) '' (direct_sum_to_R_extension (pid_to_sk_chain_to_R p m) ⁻¹' {0}))) 
  = {pid_to_pt p}
```

Given the inductive hypothesis:
```lean
ih: Subtype.val '' (pid_to_sk_chain_to_R p m ⁻¹' {0}) = {pid_to_pt p}
```

## Required Lemmas

### 1. Lemma: `direct_sum_to_R_extension` preimage of zero
**Statement:**
```lean
lemma direct_sum_to_R_extension_preimage_zero {n: ℕ} (fn: CWC.Fsk n → ℝ):
  (direct_sum_to_R_extension fn) ⁻¹' {0} = 
  {x | ∃ y: CWC.Fsk n, x = Sum.inl y ∧ fn y = 0}
```
**Purpose:** Characterize when `direct_sum_to_R_extension fn` equals 0. The key insight is that:
- For `Sum.inl x`: equals 0 when `fn x = 0`
- For `Sum.inr ⟨i, x⟩`: `cb_extension` is non-negative and equals 0 only on boundary when the boundary function is 0. But we need to show it never equals 0 (or only in cases that don't affect the result).

### 2. Lemma: `cb_extension` never equals zero (or characterization)
**Statement:**
```lean
lemma cb_extension_ne_zero_in_inner {n: ℕ} (hn: 1 ≤ n) {f: @cb_boundary n → ℝ}:
  ∀ x ∈ cb_inner, cb_extension hn f x ≠ 0
```
**Or more generally:**
```lean
lemma cb_extension_eq_zero_iff {n: ℕ} (hn: 1 ≤ n) {f: @cb_boundary n → ℝ}:
  ∀ x, cb_extension hn f x = 0 ↔ (x ∈ cb_boundary ∧ f ⟨x, _⟩ = 0)
```
**Purpose:** Understand when `cb_extension` equals 0. This is needed because `direct_sum_to_R_extension` uses `cb_extension` for the `Sum.inr` case.

### 3. Lemma: Quotient.mk preserves Sum.inl structure
**Statement:**
```lean
lemma quotient_mk_sum_inl {n: ℕ} (x: CWC.Fsk n):
  Quotient.mk _ (Sum.inl x) = left_adj_proj _ (CWC.Ff n) x
```
**Note:** This follows from the definition: `left_adj_proj A f = (adj_proj A f) ∘ (Sum.inl)` and `adj_proj A f = Quotient.mk _`, so `left_adj_proj _ (CWC.Ff n) x = Quotient.mk _ (Sum.inl x)`.

**Or more generally:**
```lean
lemma quotient_mk_image_sum_inl {n: ℕ} (S: Set (CWC.Fsk n)):
  (Quotient.mk _) '' {x | ∃ y: CWC.Fsk n, x = Sum.inl y ∧ y ∈ S} = 
  (left_adj_proj _ (CWC.Ff n)) '' S
```
**Purpose:** Understand how `Quotient.mk` maps `Sum.inl` elements. This connects the direct sum structure to the quotient structure.

### 4. Lemma: Fφ and left_adj_proj relationship
**Statement:**
```lean
lemma Fφ_left_adj_proj_inv {n: ℕ} (x: CWC.Fsk n):
  Function.invFun (CWC.Fφ n) (Quotient.mk _ (left_adj_proj _ (CWC.Ff n) x)) = 
  left_adj_proj _ (CWC.Ff n) x
```
**Or using Fφ_fix:**
```lean
lemma Fφ_inv_on_left_adj_proj_range {n: ℕ}:
  ∀ x ∈ Set.range (left_adj_proj _ (CWC.Ff n)),
    Function.invFun (CWC.Fφ n) ((CWC.Fφ n) x) = x
```
**Purpose:** Understand how `Function.invFun (CWC.Fφ n)` interacts with elements coming from `left_adj_proj`. This is needed because `Fφ_fix` tells us `(Fφ n) ∘ (left_adj_proj _ (Ff n)) = fun x ↦ ⟨x.1, (Fsk_chain n) x.2⟩`.

### 5. Lemma: Subtype.val and Fφ composition
**Statement:**
```lean
lemma subtype_val_Fφ_left_adj_proj {n: ℕ} (x: CWC.Fsk n):
  Subtype.val ((CWC.Fφ n) (left_adj_proj _ (CWC.Ff n) x)) = x.1
```
**Or using Fφ_fix:**
```lean
lemma subtype_val_Fφ_fix {n: ℕ} (x: CWC.Fsk n):
  Subtype.val ((CWC.Fφ n) (left_adj_proj _ (CWC.Ff n) x)) = x.1
```
**Purpose:** Connect `Subtype.val`, `Fφ`, and `left_adj_proj` to get back to the original element in `CWC.Fsk n`.

### 6. Lemma: Image composition with bijective functions
**Statement:**
```lean
lemma image_comp_bijective {α β γ: Type*} (f: α → β) (g: β → γ) 
  (hf: Function.Bijective f):
  g '' (f '' S) = (g ∘ f) '' S
```
**Or more specifically:**
```lean
lemma image_invFun_image {α β: Type*} (f: α → β) (hf: Function.Bijective f) (S: Set β):
  f '' (Function.invFun f '' S) = S ∩ Set.range f
```
**Purpose:** Handle the composition of images through `Function.invFun (CWC.Fφ n)` which is bijective (since `Fφ` is a homeomorphism).

### 7. Lemma: Connecting everything together
**Statement:**
```lean
lemma direct_sum_to_R_extension_preimage_zero_characterization {n: ℕ} 
  (fn: CWC.Fsk n → ℝ) (hfn: ∀ x, fn x = 0 ↔ x = ⟨pid_to_pt p, pid_to_pt_in_sk p⟩):
  Subtype.val '' ((Function.invFun (CWC.Fφ n)) '' 
    ((Quotient.mk _) '' (direct_sum_to_R_extension fn ⁻¹' {0}))) = 
  {pid_to_pt p}
```
**Purpose:** This would be the main lemma combining all the above, showing that the entire chain of operations preserves the property that only `pid_to_pt p` maps to 0.

## Strategy

The proof strategy would be:
1. Show that `direct_sum_to_R_extension fn` equals 0 only for `Sum.inl x` where `fn x = 0`
2. Use the inductive hypothesis to show that `fn x = 0` only when `x = ⟨pid_to_pt p, pid_to_pt_in_sk p⟩`
3. Show that `Quotient.mk` maps `Sum.inl x` to something related to `left_adj_proj _ (CWC.Ff n) x`
4. Use `Fφ_fix` and properties of `Function.invFun` to show that applying `Function.invFun (CWC.Fφ n)` and then `Subtype.val` gives us back `x.1 = pid_to_pt p`
5. Show that this is the only element in the resulting set

## Notes

- The key challenge is understanding how `cb_extension` behaves - it's non-negative, but we need to show it doesn't interfere with the zero preimage
- The relationship between `Fφ`, `left_adj_proj`, and `Quotient.mk` is crucial
- The inductive hypothesis `ih` gives us the base case that `pid_to_sk_chain_to_R p m` equals 0 only at `pid_to_pt p`

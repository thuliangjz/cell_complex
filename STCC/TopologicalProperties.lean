import STCC.CellComplex
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.UnitInterval
open Topology unitInterval
open BigOperators
namespace Chp5
open CellComplexClass
-- We shall not rule out the possiblity where X is empty, so is skeleton and subcomplex
structure is_disconnection {X: Type*} [TopologicalSpace X] (s: Set X) (x1 : Set X) (x2: Set X) : Prop where
  left_open: IsOpen (((↑): s → X) ⁻¹' x1)
  right_open: IsOpen (((↑): s → X) ⁻¹' x2)
  cover: s ⊆ x1 ∪ x2
  left_inter: (s ∩ x1).Nonempty
  right_inter: (s ∩ x2).Nonempty
  disjoint: Disjoint s (x1 ∩ x2)

theorem aux_is_disconnection_comm_left {X: Type*} [TopologicalSpace X] {s X1 X2 : Set X} : is_disconnection s X1 X2 → is_disconnection s X2 X1 := by
  intro h
  exact {
    left_open := h.right_open
    right_open := h.left_open
    cover := by simpa [Set.union_comm] using h.cover
    left_inter := h.right_inter
    right_inter := h.left_inter
    disjoint := by simpa [Set.inter_comm] using h.disjoint
  }

theorem aux_left_nonempty_of_disconnection {X: Type*} [TopologicalSpace X] {s x1 x2: Set X} (h: is_disconnection s x1 x2): x1.Nonempty := Set.Nonempty.right h.left_inter
theorem aux_right_nonempty_of_disconnection {X: Type*} [TopologicalSpace X] {s x1 x2: Set X} (h: is_disconnection s x1 x2): x2.Nonempty := Set.Nonempty.right h.right_inter

theorem aux_is_disconnection_comm {X: Type*} [TopologicalSpace X] {s X1 X2 : Set X} : is_disconnection s X1 X2 ↔ is_disconnection s X2 X1 := by
  constructor
  <;> apply aux_is_disconnection_comm_left

theorem aux_sub_one_partition_of_connected {X: Type*} [TopologicalSpace X] {s X1 X2: Set X} (h: is_disconnection s X1 X2) {r: Set X} (hr: r ⊆ s) (h_r_preconnected: IsPreconnected r) : r ⊆ X1 ∨ r ⊆ X2 := by
  let g : s → X := (↑)
  let r' := g ⁻¹' r
  have h_r'_mpr: r = g '' r' := by
    ext x
    simp[g]
    constructor
    case mp=>
      intro hx
      use hr hx, hx
    case mpr =>
      intro hx
      rcases hx with ⟨h1, h2⟩
      exact h2
  have r'_preconnected: IsPreconnected r' := by
    rw [h_r'_mpr] at h_r_preconnected
    have : IsInducing g := by exact Topology.IsInducing.subtypeVal
    rw [IsInducing.isPreconnected_image this] at h_r_preconnected
    exact h_r_preconnected
  let X1' := g ⁻¹' X1
  let X2' := g ⁻¹' X2
  have hX1': X1' = g ⁻¹' (s ∩ X1) := Eq.symm (Subtype.preimage_coe_self_inter s X1)
  have hX2': X2' = g ⁻¹' (s ∩ X2) := Eq.symm (Subtype.preimage_coe_self_inter s X2)
  have X1'_open : IsOpen X1' := h.left_open
  have X2'_open : IsOpen X2' := h.right_open
  have disjoint_X1'_X2' : Disjoint X1' X2' := by
    rw [hX1', hX2']
    refine Disjoint.preimage g ?_
    rw [Set.disjoint_iff]
    have : s ∩ (X1) ∩ (s ∩ X2) = s ∩ (X1 ∩ X2) := by exact Eq.symm (Set.inter_inter_distrib_left s X1 X2)
    simpa [Set.disjoint_iff, this] using h.disjoint
  have r'_in_X1'_and_X2' : r' ⊆ X1' ∪ X2' := by
    have : X1' ∪ X2' = Set.univ := by
      ext x
      constructor
      case mp => intro hx; trivial
      case mpr =>
        intro hx
        show g x ∈ X1 ∪ X2
        exact h.cover x.2
    rw [this]
    exact fun ⦃a⦄ a ↦ trivial
  have r'_in_X1'_or_r'_in_X2' : r' ⊆ X1' ∨ r' ⊆ X2' := IsPreconnected.subset_or_subset X1'_open X2'_open disjoint_X1'_X2' r'_in_X1'_and_X2' r'_preconnected
  match r'_in_X1'_or_r'_in_X2' with
  | Or.inl hr' =>
    left
    intro x hx
    rw [h_r'_mpr] at hx
    rcases hx with ⟨x', hx', rfl⟩
    exact hr' hx'
  | Or.inr hr' =>
    right
    intro x hx
    rw [h_r'_mpr] at hx
    rcases hx with ⟨x', hx', rfl⟩
    exact hr' hx'

section
variable {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X]
theorem aux_cell_closure_inter_1_partition {n : ℕ} (hn: 1 ≤ n) {X1 X2: Set X} (h: is_disconnection (Skeleton X n) X1 X2) (hX1: X1 ⊆ (Skeleton X n)) (hX2: X2 ⊆ (Skeleton X n)) : ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → ((closure e ∩ X1).Nonempty ∨ (closure e ∩ X2).Nonempty) ∧ ¬(((closure e ∩ X1).Nonempty ∧ (closure e ∩ X2).Nonempty)) := by
  intro e e_in_sets e_sub_skeleton_np1
  have : C.dim_map ⟨e, e_in_sets⟩ ≤ n ∨ C.dim_map ⟨e, e_in_sets⟩ = n + 1 := by
    have : C.dim_map ⟨e, e_in_sets⟩ ≤ n + 1 := (sub_skeleton_iff ⟨e, e_in_sets⟩).mp e_sub_skeleton_np1
    exact Nat.le_or_eq_of_le_succ this
  match this with
  | Or.inl h_e_dim =>
    have e_sub_Xn: e ⊆ Skeleton X n := by
          rw [sub_skeleton_iff ⟨e, e_in_sets⟩]
          exact h_e_dim
    have ce_sub_Xn: closure e ⊆ Skeleton X n := by
      apply (Skeleton X n).cell_closure_incl e e_in_sets e_sub_Xn
    have ce_pre_connected: IsPreconnected (closure e) := by
      exact IsConnected.isPreconnected (cell_closure_connected e e_in_sets)
    have ce_in_either : closure e ⊆ X1 ∨ closure e ⊆ X2 := by
      apply aux_sub_one_partition_of_connected h ce_sub_Xn ce_pre_connected
    wlog ce_in_X1: closure e ⊆ X1 generalizing X1 X2 h ce_in_either
    case inr =>
      rw [or_comm, @and_comm (closure e ∩ X1).Nonempty (closure e ∩ X2).Nonempty]
      apply this (aux_is_disconnection_comm_left h) hX2 hX1 (ce_in_either.symm) (ce_in_either.resolve_left ce_in_X1)
    have h1: (closure e ∩ X1).Nonempty := by
      rcases C.nonempty e e_in_sets with ⟨x₀, hx₀⟩
      use x₀
      exact ⟨subset_closure hx₀, ce_in_X1 (subset_closure hx₀)⟩
    have h2: ¬(closure e ∩ X2).Nonempty := by
      by_contra! h0
      rcases h0 with ⟨x₀, hx₀⟩
      have : x₀ ∈ X1 ∩ X2 := ⟨ce_in_X1 hx₀.1 , hx₀.2⟩
      apply Set.disjoint_iff.mp h.disjoint ⟨ce_sub_Xn hx₀.1, this⟩
    rw [not_and_or]
    exact ⟨Or.inl h1, Or.inr h2⟩
  | Or.inr h_e_dim =>
    let boundary := Set.range (cb_boundary_map (C.characteristic_map ⟨e, e_in_sets⟩))
    have boundary_connected : IsConnected boundary := by
      simp [boundary, boundary_map_range]
      apply IsConnected.image
      case H =>
        apply cb_boundary_connected
        rw [h_e_dim]
        linarith
      case hf =>
        apply Continuous.continuousOn
        exact characteristic_map_continuous ⟨e, e_in_sets⟩
    have boundary_sub_Xn : boundary ⊆ Skeleton X n := by
      trans ⋃ p:C.sets, ⋃ _:(C.dim_map p < C.dim_map ⟨e, e_in_sets⟩), p.val
      apply C.characteristic_map_boundary
      have : ∀ p : C.sets, C.dim_map p < C.dim_map ⟨e, e_in_sets⟩ → p.val ⊆ Skeleton X n := by
        intro p hp
        rw [h_e_dim] at hp
        rw [sub_skeleton_iff]
        exact Nat.le_of_lt_succ hp
      simpa using this
    have boundary_in_either : boundary ⊆ X1 ∨ boundary ⊆ X2 := by
      apply aux_sub_one_partition_of_connected h boundary_sub_Xn boundary_connected.isPreconnected
    wlog boundary_in_X1 : boundary ⊆ X1 generalizing X1 X2
    case inr =>
      rw [or_comm, @and_comm (closure e ∩ X1).Nonempty (closure e ∩ X2).Nonempty]
      apply this (aux_is_disconnection_comm_left h) hX2 hX1 (boundary_in_either.symm) (boundary_in_either.resolve_left boundary_in_X1)
    have boundary_sub_ce : boundary ⊆ closure e := by
      rw [←C.characteristic_map_range ⟨e, e_in_sets⟩]
      simp [boundary, boundary_map_range]
    have boundary_nonempty : boundary.Nonempty := by
      exact IsConnected.nonempty boundary_connected
    have h1: (closure e ∩ X1).Nonempty := by
      rcases boundary_nonempty with ⟨x₀, hx₀⟩
      use x₀
      exact ⟨boundary_sub_ce hx₀, boundary_in_X1 hx₀⟩
    have h2: ¬(closure e ∩ X2).Nonempty := by
      have ce_decomp: closure e = e ∪ boundary := by
        show closure e  = ((⟨e, e_in_sets⟩: C.sets):Set X) ∪ boundary
        rw [←C.characteristic_map_inner_range ⟨e, e_in_sets⟩, ←characteristic_map_range ⟨e, e_in_sets⟩, Set.union_comm]
        apply cb_map_range_decomposition
      have e_inter_empty: e ∩ X2 = ∅ := by
        match (Skeleton X n).cell_incl_or_disjoint e e_in_sets with
        | Or.inl h_e_in_Xn =>
          by_contra
          have : C.dim_map ⟨e, e_in_sets⟩ ≤ n := by
            rw [←sub_skeleton_iff ⟨e, e_in_sets⟩]
            simpa using h_e_in_Xn
          linarith
        | Or.inr h_e_not_in_Xn =>
          rw [Set.disjoint_iff] at h_e_not_in_Xn
          have : e ∩ X2 ⊆ e ∩ (Skeleton X n) := by
            intro x hx
            exact ⟨hx.1, hX2 hx.2⟩
          exact Set.subset_empty_iff.mp fun ⦃a⦄ a_1 ↦ h_e_not_in_Xn (this a_1)
      have boundary_inter_empty: boundary ∩ X2 = ∅ := by
        have h0: boundary ∩ X2 ⊆ X1 ∩ X2 := Set.inter_subset_inter boundary_in_X1 fun ⦃a⦄ a ↦ a
        have h1: X1 ∩ X2 = ∅ := by
          have : X1 ∩ X2 = ((Skeleton X n):Set X) ∩ (X1 ∩ X2) := by
            have : X1 ∩ X2 ⊆ (Skeleton X n) := by
              intro x hx
              exact hX1 hx.1
            exact Eq.symm (Set.inter_eq_self_of_subset_right this)
          rw [this]
          simpa [Set.disjoint_iff_inter_eq_empty] using h.disjoint
        exact Set.subset_eq_empty h0 h1
      by_contra!
      rcases this with ⟨x, hx⟩
      rw [ce_decomp, Set.inter_comm, Set.inter_union_distrib_left] at hx
      rw [Set.inter_comm, e_inter_empty, Set.inter_comm, boundary_inter_empty] at hx
      simp at hx
    rw [not_and_or]
    exact ⟨Or.inl h1, Or.inr h2⟩

-- bassically follow the method of previous theorem
theorem aux_cell_frontier_sub_left_partition {n : ℕ} (hn: 1 ≤ n) {X1 X2: Set X} (h: is_disconnection (Skeleton X n) X1 X2) (hX1: X1 ⊆ Skeleton X n) : ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → (closure e ∩ X1).Nonempty → (closure e \ e) ⊆ X1 := by
  intro e e_in_sets e_sub_skeleton_np1
  have : C.dim_map ⟨e, e_in_sets⟩ ≤ n ∨ C.dim_map ⟨e, e_in_sets⟩ = n + 1 := by
    have : C.dim_map ⟨e, e_in_sets⟩ ≤ n + 1 := (sub_skeleton_iff ⟨e, e_in_sets⟩).mp e_sub_skeleton_np1
    exact Nat.le_or_eq_of_le_succ this
  match this with
  | Or.inl h_e_dim =>
    have e_sub_Xn: e ⊆ Skeleton X n := by
          rw [sub_skeleton_iff ⟨e, e_in_sets⟩]
          exact h_e_dim
    have ce_sub_Xn: closure e ⊆ Skeleton X n := by
      apply (Skeleton X n).cell_closure_incl e e_in_sets e_sub_Xn
    have ce_pre_connected: IsPreconnected (closure e) := by
      exact IsConnected.isPreconnected (cell_closure_connected e e_in_sets)
    have ce_in_either : closure e ⊆ X1 ∨ closure e ⊆ X2 := by
      apply aux_sub_one_partition_of_connected h ce_sub_Xn ce_pre_connected
    intro hce_inter_X1_nonempty
    match ce_in_either with
    | Or.inl ce_in_X1 =>
      trans closure e
      exact diff_subset_closure_iff.mpr fun ⦃a⦄ a ↦ a
      exact ce_in_X1
    | Or.inr ce_in_X2 =>
      apply False.elim
      rcases hce_inter_X1_nonempty with ⟨x, hx⟩
      have hx_in_X1X2: x ∈ X1 ∩ X2 := ⟨hx.2, ce_in_X2 hx.1⟩
      have hx_in_Xn: x ∈ (Skeleton X n) := hX1 hx.2
      apply Set.disjoint_iff.mp h.disjoint ⟨hx_in_Xn, hx_in_X1X2⟩
  | Or.inr h_e_dim =>
    let boundary := Set.range (cb_boundary_map (C.characteristic_map ⟨e, e_in_sets⟩))
    have boundary_connected : IsConnected boundary := by
      simp [boundary, boundary_map_range]
      apply IsConnected.image
      case H =>
        apply cb_boundary_connected
        rw [h_e_dim]
        linarith
      case hf =>
        apply Continuous.continuousOn
        exact characteristic_map_continuous ⟨e, e_in_sets⟩
    have boundary_sub_Xn : boundary ⊆ Skeleton X n := by
      trans ⋃ p:C.sets, ⋃ _:(C.dim_map p < C.dim_map ⟨e, e_in_sets⟩), p.val
      apply C.characteristic_map_boundary
      have : ∀ p : C.sets, C.dim_map p < C.dim_map ⟨e, e_in_sets⟩ → p.val ⊆ Skeleton X n := by
        intro p hp
        rw [h_e_dim] at hp
        rw [sub_skeleton_iff]
        exact Nat.le_of_lt_succ hp
      simpa using this
    have boundary_in_either : boundary ⊆ X1 ∨ boundary ⊆ X2 := by
      apply aux_sub_one_partition_of_connected h boundary_sub_Xn boundary_connected.isPreconnected
    have boundary_sub_ce : boundary ⊆ closure e := by
      rw [←C.characteristic_map_range ⟨e, e_in_sets⟩]
      simp [boundary, boundary_map_range]
    have boundary_nonempty : boundary.Nonempty := by
      exact IsConnected.nonempty boundary_connected
    have ce_decomp: closure e = e ∪ boundary := by
      show closure e  = ((⟨e, e_in_sets⟩: C.sets):Set X) ∪ boundary
      rw [←C.characteristic_map_inner_range ⟨e, e_in_sets⟩, ←characteristic_map_range ⟨e, e_in_sets⟩, Set.union_comm]
      apply cb_map_range_decomposition
    have e_inter_Xn_empty : e ∩ (Skeleton X n) = ∅ := by
      show e ∩ (⋃s: C.sets, ⋃ _:(C.dim_map s ≤ n), s.val) = ∅
      rw [Set.inter_iUnion₂]
      simp
      show ∀ (i : Set X) (i_1 : i ∈ sets), dim_map ⟨i, i_1⟩ ≤ n → e ∩ i = ∅ -- we keep this show here to make simp's goal explicit
      intro s s_in_sets s_dim_less_n
      rw [←Set.disjoint_iff_inter_eq_empty]
      apply C.disjoint e_in_sets s_in_sets
      contrapose! s_dim_less_n
      have : C.dim_map ⟨s, s_in_sets⟩ = C.dim_map ⟨e, e_in_sets⟩ := by
        congr!
        exact s_dim_less_n.symm
      rw [this]
      linarith
    have e_inter_boundary_empty: e ∩ boundary = ∅ := by
      have : e ∩ boundary ⊆ e ∩ (Skeleton X n) := Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) boundary_sub_Xn
      rw [e_inter_Xn_empty] at this
      exact Set.subset_eq_empty this rfl
    have ce_sub_e_eq_boundary: closure e \ e = boundary := by
      rw [ce_decomp]
      apply Set.union_diff_cancel_left
      exact Set.subset_empty_iff.mpr e_inter_boundary_empty
    have X1X2_disjoint : X1 ∩ X2 = ∅ := by
      have : X1 ∩ X2 = ((Skeleton X n): Set X) ∩ (X1 ∩ X2) := by
        apply Set.right_eq_inter.mpr
        intro x hx
        exact hX1 hx.1
      rw [this, ←Set.disjoint_iff_inter_eq_empty]
      exact h.disjoint
    intro h_ce_inter_X1
    rw [ce_sub_e_eq_boundary]
    match boundary_in_either with
    | Or.inl bX1 => exact bX1
    | Or.inr bX2 =>
      rcases h_ce_inter_X1 with ⟨x, hx⟩
      have : x ∈ boundary ∩ X1 := by
        rw [ce_decomp] at hx
        have : X1 ∩ e = ∅ := by
          rw [Set.inter_comm]
          have : e ∩ X1 ⊆ e ∩ (Skeleton X n) := Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) hX1
          exact Set.subset_eq_empty this e_inter_Xn_empty
        rw [Set.inter_comm, Set.inter_union_distrib_left, this, Set.empty_union, Set.inter_comm] at hx
        exact hx
      have : x ∈ X1 ∩ X2 := ⟨this.2, bX2 this.1⟩
      rw [X1X2_disjoint] at this
      apply False.elim
      exact this


theorem aux_disconnection_induction [CW: CWComplexClass X] {n: ℕ} {X1 X2: Set X} (h: is_disconnection (Skeleton X n) X1 X2) (hX1: X1 ⊆ (Skeleton X n)) (hX2: X2 ⊆ (Skeleton X n)) (hn: 1 ≤ n): ∃ X1': Set X, ∃ X2' : Set X, is_disconnection (Skeleton X (n + 1)) X1' X2' ∧ X1 ⊆ X1' ∧ X2 ⊆ X2' ∧ X1' ⊆ (Skeleton X (n + 1)) ∧ X2' ⊆ (Skeleton X (n + 1)):= by
  set X1' : Set X := ⋃ e:C.sets, ⋃ _: e.1 ⊆ (Skeleton X (n + 1)) ∧ (closure e.1 ∩ X1).Nonempty, e.1 with X1'_def
  set X2' : Set X := ⋃ e:C.sets, ⋃ _: e.1 ⊆ (Skeleton X (n + 1)) ∧ (closure e.1 ∩ X2).Nonempty, e.1 with X2'_def
  use X1', X2'
  have X1'X2'_sub_Xnp1 : X1' ⊆ Skeleton X (n + 1) ∧ X2' ⊆ Skeleton X (n + 1):= by
    constructor
    repeat
    intro x hx
    simp [X1'_def, X2'_def] at hx
    rcases hx with ⟨e, he⟩
    exact he.1.1 he.2.2
  have aux_inter_only_1 : ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → ((closure e ∩ X1).Nonempty ∨ (closure e ∩ X2).Nonempty) ∧ ¬(((closure e ∩ X1).Nonempty ∧ (closure e ∩ X2).Nonempty)) := by
    apply aux_cell_closure_inter_1_partition hn h hX1 hX2
  have X1X2_sub_corresponding : X1 ⊆ X1' ∧ X2 ⊆ X2' := by
    have aux_Xi_sub_Xi': ∀ Xi: (Set X), Xi ⊆ (Skeleton X n) → Xi ⊆ ⋃ e:C.sets, ⋃ (_ : e.1 ⊆ ↑(Skeleton X (n + 1)) ∧ (closure e.1 ∩ Xi).Nonempty), e.1 := by
      intro Xi hXi
      intro x hx
      simp
      rcases mem_sub_complex_iff.mp (hXi hx) with ⟨e, e_in_sets, ⟨x_in_e, e_sub_Xn⟩⟩
      have e_sub_Xnp1 : e ⊆ Skeleton X (n + 1) := by
        rw [sub_skeleton_iff ⟨e, e_in_sets⟩]
        rw [sub_skeleton_iff ⟨e, e_in_sets⟩] at e_sub_Xn
        linarith
      have ce_inter_X1_nonempty : (closure e ∩ Xi).Nonempty := by
        use x
        exact ⟨subset_closure x_in_e, hx⟩
      use e
    constructor
    . apply aux_Xi_sub_Xi' _ hX1
    apply aux_Xi_sub_Xi' _ hX2
  have X1'X2'_eq_Xnp1 : X1' ∪ X2' = Skeleton X (n + 1) := by
    ext x
    constructor
    case h.mp =>
      intro hx
      rcases hx with x_in_X1' | x_in_X2'
      . exact X1'X2'_sub_Xnp1.1 x_in_X1'
      exact X1'X2'_sub_Xnp1.2 x_in_X2'
    case h.mpr =>
      intro hx
      rcases mem_sub_complex_iff.mp hx with ⟨e, e_in_sets, x_in_e, e_sub_Xnp1⟩
      match (aux_inter_only_1 e e_in_sets e_sub_Xnp1).1 with
      | Or.inl h_ce_X1 => left; simp [X1'_def]; use e
      | Or.inr h_ce_X2 => right; simp [X2'_def]; use e
  have X1'X2'_disjoint: X1' ∩ X2' = ∅ := by
    by_contra! h'
    rcases h' with ⟨x, x_in_X1', x_in_X2'⟩
    simp [X1'_def] at x_in_X1'
    rcases x_in_X1' with ⟨e1, ⟨he1_sub_Xnp1, ce1_inter_X1⟩, e1_in_sets, x_in_e1⟩
    simp [X2'_def] at x_in_X2'
    rcases x_in_X2' with ⟨e2, ⟨he2_sub_Xnp1, ce2_inter_X2⟩, e2_in_sets, x_in_e2⟩
    have e1_eq_e2 : e1 = e2 := by apply same_cell_of_mem e1_in_sets e2_in_sets x_in_e1 x_in_e2
    rw [←e1_eq_e2] at ce2_inter_X2
    exact (aux_inter_only_1 e1 e1_in_sets he1_sub_Xnp1).2 ⟨ce1_inter_X1, ce2_inter_X2⟩
  have X1'X2'_disjoint_Xnp1 : Disjoint ((Skeleton X (n + 1)): Set X) (X1' ∩ X2') := by
    rw [Set.disjoint_iff_inter_eq_empty, X1'X2'_disjoint]
    apply Set.inter_empty
  have aux_sub_only_1 : ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → (closure e) ⊆ X1' ∨ (closure e) ⊆ X2' := by
    intro e e_in_sets e_sub_Xnp1
    have ce_sub_Xnp1 : closure e ⊆ (Skeleton X (n + 1)) := by
      have : IsClosed ((Skeleton X (n + 1)) : Set X) := by apply sub_cw_cell_complex_closed
      rw [IsClosed.closure_subset_iff this]
      exact e_sub_Xnp1
    match (aux_inter_only_1 e e_in_sets e_sub_Xnp1).1 with
    | Or.inl he =>
      left
      have e_in_X1' : e ⊆ X1' := by
        intro x hx
        simp [X1'_def]
        use e
      have be_in_X1' : (closure e \ e) ⊆ X1' := by
        trans X1
        apply aux_cell_frontier_sub_left_partition hn h hX1 e e_in_sets e_sub_Xnp1 he
        exact X1X2_sub_corresponding.1
      rw [←(Set.union_diff_cancel' (fun ⦃a⦄ a ↦ a) subset_closure)]
      exact Set.union_subset e_in_X1' be_in_X1'
    | Or.inr he =>
      right
      have e_in_X2' : e ⊆ X2' := by
        intro x hx
        simp [X2'_def]
        use e
      have be_in_X2' : (closure e \ e) ⊆ X2' := by
        trans X2
        apply aux_cell_frontier_sub_left_partition hn (aux_is_disconnection_comm_left h) hX2 e e_in_sets e_sub_Xnp1 he
        exact X1X2_sub_corresponding.2
      rw [←(Set.union_diff_cancel' (fun ⦃a⦄ a ↦ a) subset_closure)]
      exact Set.union_subset e_in_X2' be_in_X2'
  let g : Skeleton X (n + 1) → X := (↑)
  have g_injective: Function.Injective g := by exact Subtype.val_injective
  have X1'X2'_open_in_Xnp1: IsOpen (g ⁻¹' X1') ∧ IsOpen (g ⁻¹' X2') := by
    let Y1 := g ⁻¹' X1'
    let Y2 := g ⁻¹' X2'
    show IsOpen Y1 ∧ IsOpen Y2
    have : Y2 = Y1ᶜ := by
      have union_univ : Y1 ∪ Y2 = Set.univ := by
        rw [←Set.preimage_union, X1'X2'_eq_Xnp1, ←Set.preimage_range g]
        congr!
        exact Eq.symm Subtype.range_coe
      have inter_empty: Y1 ∩ Y2 = ∅ := by
        rw [←Set.preimage_inter, X1'X2'_disjoint]
        rfl
      refine Eq.symm (compl_unique ?disj ?union)
      case disj => exact inter_empty
      case union => exact union_univ
    rw [this, isOpen_compl_iff]
    apply open_closed_of_cell_empty_or_full_intersection
    have sub_X1'_or_disjoint: ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → ((closure e) ∩ X1' = closure e) ∨ ((closure e) ∩ X1' = ∅) := by
      intro e e_in_sets e_sub_Xnp1
      match aux_sub_only_1 e e_in_sets e_sub_Xnp1 with
      | Or.inl he =>
        left
        rw [Set.inter_eq_left]
        exact he
      | Or.inr he =>
        right
        have :closure e ∩ X1' ⊆ X2' ∩ X1' := Set.inter_subset_inter he fun ⦃a⦄ a ↦ a
        rw [Set.inter_comm X2', X1'X2'_disjoint] at this
        exact Set.subset_eq_empty this rfl
    rintro e' e'_in_sets
    let e := g ''  e'
    have e_in_sets : e ∈ C.sets := e'_in_sets
    have e_sub_Xnp1 : e ⊆ (Skeleton X (n + 1)) := by
      rintro x ⟨y, hy, rfl⟩
      exact Subtype.coe_prop y
    have range_Y1: g '' Y1 = X1' := by
      apply Set.image_preimage_eq_of_subset
      rw [Subtype.range_coe]
      exact X1'X2'_sub_Xnp1.1
    have ce_eq_gce': closure e = g '' (closure e') := by
      apply IsClosedMap.closure_image_eq_of_continuous
      case f_closed =>
        apply IsClosed.isClosedMap_subtype_val
        apply sub_cw_cell_complex_closed
      case f_cont =>
        exact continuous_subtype_val
    match sub_X1'_or_disjoint e e_in_sets e_sub_Xnp1 with
    | Or.inr h1 =>
      left
      rw [←Set.image_eq_image g_injective, Set.image_empty, Set.image_inter g_injective, ←ce_eq_gce', range_Y1]
      exact h1
    | Or.inl h2 =>
      right
      rw [←Set.image_eq_image g_injective, Set.image_inter g_injective, ←ce_eq_gce', range_Y1]
      exact h2
  have X1'_cap_Xnp1_nonempty: (((Skeleton X (n + 1)): Set X) ∩ X1').Nonempty := by
    have : (((Skeleton X (n + 1)): Set X) ∩ X1') = X1' := by
      simpa [Set.left_eq_inter] using X1'X2'_sub_Xnp1.1
    rw [this]
    rcases h.left_inter with ⟨x, hx_in_Xn, hx_in_X1⟩
    use x
    exact X1X2_sub_corresponding.1 hx_in_X1
  have X2'_cap_Xnp1_nonempty: (((Skeleton X (n + 1)): Set X) ∩ X2').Nonempty := by
    have : (((Skeleton X (n + 1)): Set X) ∩ X2') = X2' := by
      simpa [Set.left_eq_inter] using X1'X2'_sub_Xnp1.2
    rw [this]
    rcases h.right_inter with ⟨x, hx_in_Xn, hx_in_X2⟩
    use x
    exact X1X2_sub_corresponding.2 hx_in_X2
  constructor
  . exact {
      left_open := X1'X2'_open_in_Xnp1.1
      right_open := X1'X2'_open_in_Xnp1.2
      cover := by rw [X1'X2'_eq_Xnp1]
      left_inter := X1'_cap_Xnp1_nonempty
      right_inter := X2'_cap_Xnp1_nonempty
      disjoint := X1'X2'_disjoint_Xnp1
    }
  tauto
end

theorem connected_1_skeleton_of_connected {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X] [PreconnectedSpace X] : IsPreconnected ((Skeleton X 1): Set X) := by
  by_contra! hc
  simp [IsPreconnected] at hc
  rcases hc with ⟨Y1, Y1_open, Y2, Y2_open, Y1Y2_cover_1sk, Y1_inter_nonempty, Y2_inter_nonempty, Y1Y2_inter_empty⟩
  set X1 := Y1 ∩ (Skeleton X 1) with X1_def
  set X2 := Y2 ∩ (Skeleton X 1) with X2_def
  have hX1X2_disconnection: is_disconnection (Skeleton X 1) X1 X2 := by
    let g : ((Skeleton X 1): Set X) → X := (↑)
    exact {
      left_open := by
        rw [Subtype.preimage_coe_inter_self]
        exact IsOpen.preimage_val Y1_open
      right_open := by
        rw [Subtype.preimage_coe_inter_self]
        exact IsOpen.preimage_val Y2_open
      cover := by
        rw [X1_def, X2_def]
        intro x hx
        rcases Y1Y2_cover_1sk hx with x_in_Y1 | x_in_Y2
        case inl =>
          left
          exact ⟨x_in_Y1, hx⟩
        case inr =>
          right
          exact ⟨x_in_Y2, hx⟩
      left_inter := by
        rw [X1_def, Set.inter_comm, Set.inter_assoc, Set.inter_self, Set.inter_comm]
        exact Y1_inter_nonempty
      right_inter := by
        rw [X2_def, Set.inter_comm, Set.inter_assoc, Set.inter_self, Set.inter_comm]
        exact Y2_inter_nonempty
      disjoint := by
        rw [Set.disjoint_iff_inter_eq_empty]
        have : ((Skeleton X 1): Set X) ∩ (X1 ∩ X2) = ((Skeleton X 1): Set X) ∩ (Y1 ∩ Y2) := by
          simp[X1_def, X2_def]
          ext x
          constructor
          . intro hx
            exact ⟨hx.1, ⟨hx.2.1.1, hx.2.2.1⟩⟩
          intro hx
          tauto
        rw [this]
        contrapose! Y1Y2_inter_empty
        exact Y1Y2_inter_empty
    }
  choose fx1 fx2 h_disconnection h_x1_sub_fx1 h_x2_sub_fx2 h_fx_sub_sknp1 using @aux_disconnection_induction X _ _ C CW
  have seq_fun: ∃ f: ℕ → (Set X × Set X), ∀ n : ℕ, (is_disconnection (Skeleton X (n + 1)) (f n).1 (f n).2) ∧ (f n).1 ⊆ (Skeleton X (n + 1)) ∧ (f n).2 ⊆ (Skeleton X (n + 1)) ∧ (f n).1 ⊆ (f (n + 1)).1 ∧ (f n).2 ⊆ (f (n + 1)).2:= by
    let p : (ℕ × Set X × Set X) → Prop := fun ⟨n, s1, s2⟩ ↦ is_disconnection (Skeleton X (n + 1)) s1 s2 ∧ s1 ⊆ (Skeleton X (n + 1)) ∧ s2 ⊆ (Skeleton X (n + 1))
    let r : (Set X × Set X) → (Set X × Set X) → Prop := fun ⟨s1, s2⟩ ⟨s1', s2'⟩ ↦ s1 ⊆ s1' ∧ s2 ⊆ s2'
    -- the subtype constructor here is just a work-around to allow carry proposition in sigma type
    let φ : (n : ℕ) → Σx : (Set X × Set X), {y: Set X // p ⟨n, x⟩}  := by
      intro n
      induction' n with n ihn
      case zero =>
        have : p ⟨0, ⟨X1, X2⟩⟩ := by
          simp [p]
          have X1_sub_SK1 : X1 ⊆ Skeleton X 1 := by rw [X1_def]; exact Set.inter_subset_right
          have X2_sub_Sk1 : X2 ⊆ Skeleton X 1 := by rw [X2_def]; exact Set.inter_subset_right
          exact ⟨hX1X2_disconnection, X1_sub_SK1, X2_sub_Sk1⟩
        exact ⟨⟨X1, X2⟩, ⟨X1, this⟩⟩
      case succ =>
        rcases ihn with ⟨⟨Xₙ₁, Xₙ₂⟩, ⟨_, h⟩⟩
        let Xₙ₁': Set X := fx1 h.1 h.2.1 h.2.2 (by norm_num)
        let Xₙ₂': Set X := fx2 h.1 h.2.1 h.2.2 (by norm_num)
        have : p ⟨(n + 1), Xₙ₁', Xₙ₂'⟩ := by
          simp [p]
          have aux_disconnection: is_disconnection (↑(Skeleton X (n + 1 + 1))) Xₙ₁' Xₙ₂' := by apply h_disconnection
          have aux_subset: Xₙ₁' ⊆ ↑(Skeleton X (n + 1 + 1)) ∧ Xₙ₂' ⊆ ↑(Skeleton X (n + 1 + 1)) := by apply h_fx_sub_sknp1
          exact ⟨aux_disconnection, aux_subset⟩
        exact ⟨⟨Xₙ₁', Xₙ₂'⟩, ⟨Xₙ₁', this⟩⟩
    let f : ℕ → (Set X × Set X) := fun n ↦ (φ n).1
    use f
    intro n
    have p_satisfied : is_disconnection (↑(Skeleton X (n + 1))) (f n).1 (f n).2 ∧ (f n).1 ⊆ ↑(Skeleton X (n + 1)) ∧ (f n).2 ⊆ ↑(Skeleton X (n + 1)) := by
      show p ⟨n, f n⟩
      exact (φ n).2.2
    have r_satisified: (f n).1 ⊆ (f (n + 1)).1 ∧ (f n).2 ⊆ (f (n + 1)).2 := by
      -- this is possible because we have written φ EXPLICITLY instead of using choose
      have sub1: (f n).1 ⊆ (f (n + 1)).1 := by apply h_x1_sub_fx1
      have sub2: (f n).2 ⊆ (f (n + 1)).2 := by apply h_x2_sub_fx2
      tauto
    tauto
  rcases seq_fun with ⟨f, hf⟩
  -- We wish to prove Z1 and Z2 form a disconnection of univ
  set Z1 := ⋃ n:ℕ, (f n).1 with Z1_def
  set Z2 := ⋃ n:ℕ, (f n).2 with Z2_def
  have Z1_nonempty: Z1.Nonempty := by
    have : (f 0).1 ⊆ Z1 := Set.subset_iUnion_of_subset 0 fun ⦃a⦄ a ↦ a
    apply Set.Nonempty.mono this
    apply aux_left_nonempty_of_disconnection (hf 0).1
  have Z2_nonempty: Z2.Nonempty := by
    have : (f 0).2 ⊆ Z2 := Set.subset_iUnion_of_subset 0 fun ⦃a⦄ a ↦ a
    apply Set.Nonempty.mono this
    apply aux_right_nonempty_of_disconnection (hf 0).1
  have aux_f_mono: ∀ (m n : ℕ), m ≤ n → (f m).1 ⊆ (f n).1 ∧ (f m).2 ⊆ (f n).2 := by
    intro m n hmn
    induction' n with n ihn
    case zero =>
      have : m = 0 := Nat.eq_zero_of_le_zero hmn
      simp [this]
    case succ =>
      rw [Nat.le_succ_iff] at hmn
      rcases hmn with m_le_n | m_eq_np1
      case inl =>
        have : (f n).1 ⊆ (f (n + 1)).1 ∧ (f n).2 ⊆ (f (n + 1)).2 := by
          rcases hf n with ⟨h0, h1, h2, h3⟩
          exact h3
        exact ⟨fun x hx↦ this.1 ((ihn m_le_n).1 hx), fun x hx ↦ this.2 ((ihn m_le_n).2 hx)⟩
      case inr =>
        simp [m_eq_np1]
  have aux_f_disjoint: ∀ (m n : ℕ), Disjoint (f m).1 (f n).2 := by
    have aux : ∀ n: ℕ, Disjoint (f n).1 (f n).2 := by
      intro n
      rw [Set.disjoint_iff_inter_eq_empty]
      rcases hf n with ⟨h1, h2, h3, h4⟩
      have eq1: (f n).1 = (f n).1 ∩ (Skeleton X (n + 1)) := by
        rw [Set.left_eq_inter]
        exact h2
      have eq2: (f n).2 = (f n).2 ∩ (Skeleton X (n + 1)) := by
        rw [Set.left_eq_inter]
        exact h3
      calc
        (f n).1 ∩ (f n).2 = ((f n).1 ∩ (Skeleton X (n + 1))) ∩ ((f n).2 ∩ (Skeleton X (n + 1))) := by nth_rw 1 [eq1, eq2]
        _                 = ((f n).1 ∩ (f n).2) ∩ (Skeleton X (n + 1)):= by rw [Set.inter_inter_distrib_right (f n).1 (f n).2 (Skeleton X (n + 1))]
        _                 = ((Skeleton X (n + 1)): Set X) ∩ ((f n).1 ∩ (f n).2) := by rw[Set.inter_comm]
        _                 = ∅ := by rw [←Set.disjoint_iff_inter_eq_empty]; exact h1.disjoint
    intro m n
    rcases le_or_gt m n with m_le_n | n_lt_m
    case inl => exact Set.disjoint_of_subset (aux_f_mono m n m_le_n).1 (fun x h ↦ h) (aux n)
    case inr => exact Set.disjoint_of_subset (fun x h ↦ h) (aux_f_mono n m (le_of_lt n_lt_m)).2 (aux m)
  have Z1Z2_disjoint : Disjoint Z1 Z2 := by
    rw [Set.disjoint_left]
    intro x x_in_Z1
    by_contra x_in_Z2
    rw [Set.mem_iUnion] at x_in_Z1
    rw [Set.mem_iUnion] at x_in_Z2
    rcases x_in_Z1 with ⟨m, hm⟩
    rcases x_in_Z2 with ⟨n, hn⟩
    apply Set.disjoint_left.mp (aux_f_disjoint m n) hm hn
  have Z1Z2_cover : Z1 ∪ Z2 = Set.univ := by
    ext x
    constructor
    case h.mp => intro hx; trivial
    case h.mpr =>
      intro hx
      rw [←skeleton_cover, Set.mem_iUnion] at hx
      rcases hx with ⟨n₀, h_skn₀⟩
      have h_skn₀p1 : x ∈ Skeleton X (n₀ + 1) := skeleton_mono n₀ (n₀ + 1) (Nat.le_succ n₀) h_skn₀
      match (hf n₀).1.cover h_skn₀p1 with
      | Or.inl x_in_first => left; simp [Z1_def]; use n₀
      | Or.inr x_in_second => right; simp [Z2_def]; use n₀
  have Z1Z2Open : IsOpen Z1 ∧ IsOpen Z2 := by
    have : Z2 = Z1ᶜ := by
      refine Eq.symm (compl_unique ?disj ?union)
      case disj => exact Z1Z2_disjoint.inter_eq
      case union => exact Z1Z2_cover
    rw [this, isOpen_compl_iff]
    apply open_closed_of_cell_empty_or_full_intersection
    have aux_ce_sub_only_one: ∀ e ∈ C.sets, (closure e) ⊆ Z1 ∨ (closure e) ⊆ Z2 := by
      intro e e_in_sets
      let n := C.dim_map ⟨e, e_in_sets⟩
      have e_in_skn : e ⊆ (Skeleton X (n + 1)) := by
        intro x x_in_e
        show x ∈ ⋃s:C.sets, ⋃_:(C.dim_map s ≤ (n + 1)), s.val
        rw [Set.mem_iUnion₂]
        use ⟨e, e_in_sets⟩, Nat.le_succ n
      have ce_in_skn : closure e ⊆ (Skeleton X (n + 1)) := (Skeleton X (n + 1)).cell_closure_incl e e_in_sets e_in_skn
      rcases hf n with ⟨h_disconnection, hfn1, hfn2, hfnnp1⟩
      have : (closure e) ⊆ (f n).1 ∨ (closure e) ⊆ (f n).2 := by apply aux_sub_one_partition_of_connected h_disconnection ce_in_skn (IsConnected.isPreconnected (cell_closure_connected e e_in_sets))
      match aux_sub_one_partition_of_connected h_disconnection ce_in_skn (IsConnected.isPreconnected (cell_closure_connected e e_in_sets)) with
      | Or.inl ce_in_fn1 =>
        left
        rw [Z1_def]
        intro x hx
        rw [Set.mem_iUnion]
        use n
        exact ce_in_fn1 hx
      | Or.inr ce_in_fn2 =>
        right
        rw [Z2_def]
        intro x hx
        rw [Set.mem_iUnion]
        use n
        exact ce_in_fn2 hx
    intro e e_in_sets
    match aux_ce_sub_only_one e e_in_sets with
    | Or.inl e_sub_Z1 =>
      right
      rw [eq_comm, Set.left_eq_inter]
      exact e_sub_Z1
    | Or.inr e_sub_Z2 =>
      left
      rw [←Set.disjoint_iff_inter_eq_empty, disjoint_comm]
      exact Set.disjoint_of_subset (fun x hx ↦ hx) e_sub_Z2 Z1Z2_disjoint
  have univ_preconnected: @IsPreconnected X _ Set.univ := isPreconnected_univ
  have univ_not_preconnected: ¬(@IsPreconnected X _ Set.univ) := by
    simp [IsPreconnected]
    use Z1, Z1Z2Open.1, Z2, Z1Z2Open.2, Z1Z2_cover, Z1_nonempty, Z2_nonempty
    rw [Set.not_nonempty_iff_eq_empty, ←Set.disjoint_iff_inter_eq_empty]
    exact Z1Z2_disjoint
  contradiction

-- proving d=>a
section
-- path connectedness requires set to be nonempty
theorem path_connected_of_discrete_connected {X: Type*} [TopologicalSpace X] {s: Set X} (hs: DiscreteTopology s) (cs: IsConnected s) : IsPathConnected s := by
  have aux: ∀ x ∈ s, ∀ y ∈ s, x = y := by
    intro x hx y hy
    by_contra! x_ne_y
    let x' : s := ⟨x, hx⟩
    let y' : s := ⟨y, hy⟩
    have x'_ne_y': x' ≠ y' := Subtype.coe_ne_coe.mp x_ne_y
    have univ_preconnected: @IsPreconnected s _ Set.univ := preconnectedSpace_iff_univ.mp (isConnected_iff_connectedSpace.mp cs).toPreconnectedSpace
    have univ_not_preconnected: ¬(@IsPreconnected s _ Set.univ) := by
      simp [IsPreconnected]
      let s1 : Set s := {x'}
      let s2 : Set s := {z | z ≠ x'}
      have cover: s1 ∪ s2 = Set.univ := by
        exact Set.compl_subset_iff_union.mp fun ⦃a⦄ a ↦ a
      have s1_nonempty : s1.Nonempty := Set.singleton_nonempty x'
      have s2_nonempty : s2.Nonempty := Set.nonempty_of_mem (id (Ne.symm x'_ne_y'))
      have s1_inter_s2_empty: s1 ∩ s2 = ∅ := Set.singleton_inter_eq_empty.mpr fun a ↦ a rfl
      use s1, s2, cover, s1_nonempty, s2_nonempty
      rwa [Set.not_nonempty_iff_eq_empty]
    contradiction
  rw [isPathConnected_iff]
  use cs.nonempty
  intro x hx y hy
  rw [aux x hx y hy]
  exact JoinedIn.refl hy
theorem subset_eq_univ_of_open_closed {X: Type*} [TopologicalSpace X] [ConnectedSpace X] {s : Set X} (s_nonempty: s.Nonempty) (s_open_closed: IsOpen s ∧ IsClosed s) : s = Set.univ := by
  suffices compl_empty: sᶜ = ∅ by
    exact Set.compl_empty_iff.mp compl_empty
  by_contra! compl_nonempty
  have compl_open: IsOpen sᶜ := by
    rw [isOpen_compl_iff]
    exact s_open_closed.2
  have : ¬ (IsPreconnected (Set.univ:Set X)) := by
    simp [IsPreconnected]
    use s, s_open_closed.1, sᶜ, compl_open, Set.union_compl_self s, s_nonempty, compl_nonempty
    simp
  have : IsPreconnected ((Set.univ:Set X)) := by
    exact isPreconnected_univ
  contradiction
theorem path_connected_in_subtype_of_path_connected {X: Type*} [TopologicalSpace X] {s1 s2: Set X} (hs1: IsPathConnected s1) (hs1s2: s1 ⊆ s2) : IsPathConnected {y:s2 | y.1 ∈ s1} := by
  let s1' := {y:s2 | y.1 ∈ s1}
  show IsPathConnected s1'
  rcases hs1 with ⟨x, x_in_s1, hx⟩
  let x':s2 := ⟨x, hs1s2 x_in_s1⟩
  use x', x_in_s1
  intro y' hy'
  rcases hx hy' with ⟨γ, hγ⟩
  let γ' : I → s2 := fun t ↦ ⟨γ t, hs1s2 (hγ t)⟩
  have cont: Continuous γ' := by continuity
  have sub: ∀ t:I, γ' t ∈ s1' := by exact hγ
  have hγ'₀ : γ' 0 = x' := SetCoe.ext γ.source
  have hγ'₁ : γ' 1 = y' := SetCoe.ext γ.target
  exact ⟨⟨⟨γ', cont⟩, hγ'₀, hγ'₁⟩, sub⟩
theorem cell_closure_sub_component_of_inter {X: Type*} [TopologicalSpace X] [T2Space X] [CellComplexClass X] {x: X} {e: Set X} (e_in_sets: e ∈ sets) {y: X} (hy: y ∈ closure e ∩ pathComponent x) : closure e ⊆ pathComponent x := by
  intro z hz
  have zy_joined : Joined z y := JoinedIn.joined (IsPathConnected.joinedIn (cell_closure_path_connected e e_in_sets) z hz y hy.1)
  have yx_joined : Joined y x := by
    apply Joined.symm
    rw [←mem_pathComponent_iff]
    exact hy.2
  rw [mem_pathComponent_iff]
  exact Joined.trans (id (Joined.symm yx_joined)) (id (Joined.symm zy_joined))
end

theorem path_connected_of_connected_skeleton {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X] {n : ℕ} (h: IsConnected ((Skeleton X n):Set X)) : PathConnectedSpace X := by
  --refine pathConnectedSpace_iff_univ.mpr ?_
  rw [pathConnectedSpace_iff_univ]
  have skn_path_connected : IsPathConnected ((Skeleton X n):Set X) := by
    match Nat.eq_or_lt_of_le (Nat.zero_le n) with
    | Or.inl n_eq_0 =>
      rw [←n_eq_0] at h
      rw [←n_eq_0]
      apply path_connected_of_discrete_connected skeleton0_discrete h
    | Or.inr n_gt_0 =>
      -- it seems not necessary to assume n > 0
      rw [isPathConnected_iff_pathConnectedSpace]
      show PathConnectedSpace ((Skeleton X n):Set X)
      rcases h.nonempty with ⟨x, hx⟩
      let x₀ : (Skeleton X n) := ⟨x, hx⟩
      let S : (Set (Skeleton X n)) := pathComponent x₀
      suffices S_eq_univ: S = Set.univ by
        rw [pathConnectedSpace_iff_univ, ←S_eq_univ]
        exact isPathConnected_pathComponent
      have : ConnectedSpace ((Skeleton X n):Set X) := by
        rw [←isConnected_iff_connectedSpace]
        exact h
      refine subset_eq_univ_of_open_closed ?nonempty ?open_closed
      case nonempty => exact pathComponent.nonempty x₀
      case open_closed =>
        apply open_closed_of_cell_empty_or_full_intersection
        intro e₀ he₀
        match eq_or_ne (closure e₀ ∩ S) ∅ with
        | Or.inl inter_empty => left; exact inter_empty
        | Or.inr inter_nonempty =>
          rw [←Set.nonempty_iff_ne_empty] at inter_nonempty
          rcases inter_nonempty with ⟨y₀, hy₀⟩
          have : closure e₀ ⊆ S := by apply cell_closure_sub_component_of_inter he₀ hy₀
          right; apply Eq.symm;
          rwa [Set.left_eq_inter]
  have aux : ∀ m : ℕ, n ≤ m → IsPathConnected ((Skeleton X m):Set X) := by
    intro m hm
    rcases Nat.exists_eq_add_of_le hm with ⟨k, rfl⟩
    induction' k with k ihk
    case zero => simpa using skn_path_connected
    case succ =>
      have sk_npk_path_connected: IsPathConnected ((Skeleton X (n + k)): Set X) := by
        apply ihk
        exact Nat.le_add_right n k
      rw [isPathConnected_iff_pathConnectedSpace]
      let Xnk1 := Skeleton X (n + (k + 1))
      show PathConnectedSpace (Xnk1:Set X)
      let S := {x: Xnk1 | x.1 ∈ (Skeleton X (n + k))}
      have S_path_connected : IsPathConnected S := by
        apply path_connected_in_subtype_of_path_connected sk_npk_path_connected
        apply skeleton_mono
        norm_num
      have ⟨x, x_in_S, hx⟩ := S_path_connected
      let S₁ := pathComponent x
      have S_sub_S₁ : S ⊆ S₁ := S_path_connected.subset_pathComponent x_in_S
      suffices S₁_eq_univ : S₁ = Set.univ by
        rw [pathConnectedSpace_iff_univ, ←S₁_eq_univ]
        exact isPathConnected_pathComponent
      suffices cell_closure_subset : ∀ e ∈ sets, (closure e) ⊆ S₁ by
        ext x
        refine Iff.intro ?mp ?mpr
        case mp => exact fun x ↦ trivial
        case mpr =>
          intro _
          rcases exists_mem_of_cell x with ⟨e, e_in_sets, x_in_e⟩
          have : e ⊆ closure e := by exact subset_closure
          apply cell_closure_subset e e_in_sets
          apply subset_closure x_in_e
      intro e he
      let g: Xnk1 → X := (↑)
      have : dim_map ⟨e, he⟩ ≤ (n + k + 1) := by
        let e₀ := g '' e
        have e₀_in_sets : e₀ ∈ sets := he
        have e₀_sub_Xnk1 : e₀ ⊆ Xnk1 := by
          rintro x ⟨y, y_in_e, rfl⟩
          exact y.2
        rw [sub_skeleton_iff ⟨e₀, he⟩] at e₀_sub_Xnk1
        have dim_map_eq: dim_map ⟨e, he⟩ = dim_map ⟨e₀, he⟩ := rfl
        rw [dim_map_eq]
        linarith
      rw [Nat.le_succ_iff_eq_or_le] at this
      match this with
      | Or.inr dim_le_npk =>
        have e_sub_S : e ⊆ S := by
          let e₀ := g '' e
          have : dim_map ⟨e₀, he⟩ ≤ n + k := dim_le_npk
          rw [←sub_skeleton_iff] at this
          intro x₀ hx₀
          have gx₀_mem_e₀: g x₀ ∈ e₀ := by exact Set.mem_image_of_mem g hx₀
          exact this gx₀_mem_e₀
        rcases nonempty e he with ⟨y, hy⟩
        have y_in_ce_inter_S₁ : y ∈ closure e ∩ S₁ := ⟨subset_closure hy, S_sub_S₁ (e_sub_S hy)⟩
        apply cell_closure_sub_component_of_inter he y_in_ce_inter_S₁
      | Or.inl dim_eq_npkp1 =>
        let boundary := Set.range (cb_boundary_map (characteristic_map ⟨e, he⟩))
        have boundary_sub_S : boundary ⊆ S := by
          trans ⋃ p:sets, ⋃ _:(dim_map p < dim_map ⟨e, he⟩), p.val
          . apply characteristic_map_boundary
          intro x₀ hx₀
          simp at hx₀
          rcases hx₀ with ⟨p, ⟨⟨p_in_sets, hp⟩, x₀_in_p⟩⟩
          rw [dim_eq_npkp1, Nat.lt_succ] at hp
          suffices g '' p ⊆ Skeleton X (n + k) by
            simp [S]
            show g x₀ ∈ Skeleton X (n + k)
            apply this
            exact Set.mem_image_of_mem g x₀_in_p
          rw [sub_skeleton_iff ⟨g '' p, p_in_sets⟩]
          exact hp
        have boundary_sub_ce : boundary ⊆ (closure e) := by
          show Set.range (cb_boundary_map (characteristic_map ⟨e, he⟩)) ⊆ (closure e)
          rw [boundary_map_range, ←characteristic_map_range ⟨e, he⟩]
          apply Set.image_subset_range
        have boundary_nonempty' : boundary.Nonempty := by
          apply boundary_nonempty
          rw [dim_eq_npkp1]
          exact NeZero.one_le
        rcases boundary_nonempty' with ⟨x₀, hx₀⟩
        have : x₀ ∈ (closure e) ∩ S₁ := by
          exact ⟨boundary_sub_ce hx₀, S_sub_S₁ (boundary_sub_S hx₀)⟩
        exact cell_closure_sub_component_of_inter he this
  rcases h.nonempty with ⟨x₀, hx₀⟩
  use x₀, trivial
  intro y hy
  rw [←skeleton_cover_any_ge_n n, Set.mem_iUnion₂] at hy
  rcases hy with ⟨m, n_le_m, y_in_sk_m⟩
  exact ((aux m n_le_m).joinedIn x₀ (skeleton_mono n m n_le_m hx₀) y y_in_sk_m).mono (fun x hx ↦ trivial)

-- finite cell complex
def FiniteCellComplex (X: Type*) [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] : Prop := C.sets.Finite

section
variable {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X]
def dim0_cell_subcomplex (e : C.sets) (he: C.dim_map e = 0) : SubCellComplex X where
    carrier := e.1
    cell_incl_or_disjoint := by
        intro e' he'
        match eq_or_ne e' e with
        | Or.inl eq => left; rw [eq]
        | Or.inr ne => right; apply C.disjoint he' e.2 ne
    cell_closure_incl := by
        intro e' he' e'_in_e
        rw [cell_singleton_of_dim0] at he
        rcases he with ⟨x, hx⟩
        rw [hx, Set.subset_singleton_iff_eq] at e'_in_e
        match e'_in_e with
        | Or.inl e'_empty =>
            rw [e'_empty]
            simp
        | Or.inr e'_singleton =>
            rw [e'_singleton]
            simp [hx]
theorem dim0_cell_subcomplex_finite (e: C.sets) (he: C.dim_map e = 0) : FiniteCellComplex (dim0_cell_subcomplex e he) := by
    have : (sub_cell_complex_sets (dim0_cell_subcomplex e he)).Finite := by
        have : (sub_cell_complex_sets (dim0_cell_subcomplex e he)) = {Set.univ} := by
            ext e'
            let g : (dim0_cell_subcomplex e he) → X := (↑)
            have range_eq_e: g '' (Set.univ) = e.1 := by
                simp
                rw [Subtype.range_coe]
                rfl
            refine Iff.intro ?mp ?mpr
            case mp =>
                intro he'
                show e' = Set.univ
                suffices g '' e' = g '' (Set.univ) by
                    rw [Set.image_eq_image (Subtype.val_injective)] at this
                    exact this
                rw [range_eq_e]
                have e'_image_nonempty : (g '' e') ≠ ∅ := by
                    rw [←Set.nonempty_iff_ne_empty]
                    apply nonempty
                    exact he'
                have e'_image_sub_e : (g '' e') ⊆ e := by
                    rw [←range_eq_e]
                    exact Set.image_mono fun ⦃a⦄ a ↦ trivial
                rw [cell_singleton_of_dim0] at he
                rcases he with ⟨x, hx⟩
                rw [hx, Set.subset_singleton_iff_eq] at e'_image_sub_e
                rw [hx]
                tauto
            case mpr =>
                intro he'
                simp at he'
                rw [he']
                show g '' (Set.univ) ∈ C.sets
                rw [range_eq_e]
                exact e.2
        rw [this]
        apply Set.finite_singleton
    exact this

theorem finite_sub_cell_complex_iff (sc: SubCellComplex X) : (FiniteCellComplex sc) ↔ ({e:Set X| e ∈ C.sets ∧ e ⊆ sc}.Finite) := by
    let g : sc → X := (↑)
    let s1 := {e: Set X | e ∈ C.sets ∧ e ⊆ sc}
    have : s1 =  (Set.image g) '' (sub_cell_complex_sets sc) := by
        ext e
        refine Iff.intro ?mp ?mpr
        case mp =>
            intro he
            let e' := g ⁻¹' e
            use e'
            have : g '' e' = e := by
                calc
                    g '' e' = (sc:Set X) ∩ e:= Subtype.image_preimage_coe sc e
                    _ = e := Set.inter_eq_self_of_subset_right he.2
            constructor
            . show g '' e' ∈ C.sets
              rw [this]
              exact he.1
            exact this
        case mpr =>
            intro he
            simp at he
            rcases he with ⟨e', he', rfl⟩
            constructor
            . exact he'
            apply Subtype.coe_image_subset
    refine Iff.intro ?mp ?mpr
    case mp =>
        simp only [s1, this]
        intro h
        apply Set.Finite.image
        exact h
    case mpr =>
        simp only [s1, this]
        intro h
        apply Set.Finite.of_finite_image h
        apply Set.injOn_of_injective
        rw [Set.image_injective]
        exact Subtype.val_injective


theorem cell_colsure_subset_finite_sub_complex [CW: CWComplexClass X] : ∀ e ∈ C.sets, ∃ SC: (SubCellComplex X), FiniteCellComplex SC ∧ closure e ⊆ SC := by
    intro e he
    -- see "induction tactic that doesn't destroy the input from context" on Zulip chat, this usage is interesting
    -- the cases tactic can also be used in this fashion
    induction' dim_eq: (C.dim_map ⟨e, he⟩) using Nat.strong_induction_on with n₀ ihn generalizing e he
    choose f_to_subcomplex hf_finite hf_cover using ihn
    rcases boundary_covered_by_finite_cells ⟨e, he⟩ with ⟨ss, ss_sub_sets, ss_finite, ss_cover_boundary, ss_dim_lt⟩
    --let fss: ss → SubCellComplex X := by
    --    intro e
    --    let m := C.dim_map ⟨e.1, ss_sub_sets e.2⟩
    --    have m_le_n₀: m < n₀ := by
    --        rw [←dim_eq]
    --        apply ss_dim_lt _ e.2
    --    exact f_to_subcomplex m m_le_n₀ e.1 (ss_sub_sets e.2) rfl
    let fss : ss → SubCellComplex X := fun e ↦ f_to_subcomplex (C.dim_map ⟨e.1, ss_sub_sets e.2⟩) (by rw [←dim_eq]; apply ss_dim_lt _ e.2) e.1 (ss_sub_sets e.2) rfl
    let SC_carrier : Set X:= (⋃ s:ss, ((fss s):Set X)) ∪ e
    have SC_carrier_cell_incl_or_disjoint : ∀ e₁ ∈ C.sets, e₁ ⊆ SC_carrier ∨ Disjoint e₁ SC_carrier := by
        intro e₁ he₁
        match eq_or_ne (e₁ ∩ SC_carrier) ∅ with
        | Or.inl inter_eq_empty =>
            right
            rwa [Set.disjoint_iff_inter_eq_empty]
        | Or.inr inter_ne_empty =>
            left
            rw [←Set.nonempty_iff_ne_empty] at inter_ne_empty
            rcases inter_ne_empty with ⟨x, hx⟩
            match hx.2 with
            | Or.inl mem_iunion =>
                rw [Set.mem_iUnion] at mem_iunion
                rcases mem_iunion with ⟨i ,hi⟩
                suffices sub_fss_i : e₁ ⊆ (fss i) by
                    have : ((fss i):Set X) ⊆ (⋃ s, (fss s):Set X) := Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
                    tauto
                apply (fss i).subset_of_intersect he₁
                rw [←Set.nonempty_iff_ne_empty]
                use x, hx.1, hi
            | Or.inr mem_e =>
                rw [same_cell_of_mem he₁ he hx.1 mem_e]
                exact Set.subset_union_right
    have aux_sub_some_fss {e₀: Set X} (e₀_in_sets: e₀ ∈ C.sets) (e₀_sub_SC: e₀ ⊆ SC_carrier) (e₀_ne_e: e₀ ≠ e) : ∃ s:ss, e₀ ⊆ (fss s) := by
        by_contra! not_subset
        have e₀_e_disjoint : Disjoint e₀ e := C.disjoint e₀_in_sets he e₀_ne_e
        have e₀_iufss_disjoint: Disjoint e₀ (⋃s:ss, fss s) := by
            rw [Set.disjoint_iUnion_right]
            intro s
            rcases (fss s).cell_incl_or_disjoint e₀ e₀_in_sets with h_incl | h_disj
            . exact False.elim ((not_subset s) h_incl)
            exact h_disj
        have e₀_disjoint_sc: Disjoint e₀ SC_carrier := Disjoint.union_right e₀_iufss_disjoint e₀_e_disjoint
        have e₀_empty : e₀ = ∅ := by
            rw [←Set.subset_empty_iff]
            exact e₀_disjoint_sc (fun _ a ↦ a) e₀_sub_SC
        have e₀_nonempty: e₀ ≠ ∅ := by
            rw [←Set.nonempty_iff_ne_empty]
            apply C.nonempty _ e₀_in_sets
        contradiction
    have ce_sub_SC : (closure e) ⊆ SC_carrier := by
        intro x hx
        rw [←Set.inter_union_diff (closure e) e, Set.inter_eq_right.mpr subset_closure] at hx
        match hx with
        | Or.inl x_in_e =>
            apply Set.subset_union_right x_in_e
        | Or.inr x_in_e_boundary =>
            simp at ss_cover_boundary
            suffices ⋃₀ ss ⊆ SC_carrier by
                exact this (ss_cover_boundary x_in_e_boundary)
            intro x' hx'
            simp at hx'
            left
            simp
            rcases hx' with ⟨i, i_in_ss, hi⟩
            use i, i_in_ss
            apply hf_cover
            apply subset_closure hi
    have SC_carrier_cell_closure_incl : ∀ e₁ ∈ C.sets, e₁ ⊆ SC_carrier → (closure e₁) ⊆ SC_carrier := by
        intro e₁ e₁_in_sets e₁_sub_carrier
        match eq_or_ne e₁ e with
        | Or.inl heq =>
            rw [heq]
            exact ce_sub_SC
        | Or.inr hne =>
            suffices ∃ s : ss, e₁ ⊆ fss s by
                rcases this with ⟨s, hs⟩
                have ce₁_subset: (closure e₁) ⊆ fss s := (fss s).cell_closure_incl e₁ e₁_in_sets hs
                have fss_s_subset: ((fss s):Set X) ⊆ SC_carrier := by
                    intro x hx
                    left
                    exact Set.mem_iUnion_of_mem s hx
                exact fun ⦃a⦄ a_1 ↦ fss_s_subset (ce₁_subset a_1)
            exact aux_sub_some_fss e₁_in_sets e₁_sub_carrier hne
    have SC_finite : {e₀:Set X | e₀ ∈ C.sets ∧ e₀ ⊆ SC_carrier}.Finite := by
        let SE := {e₀:Set X | e₀ ∈ C.sets ∧ e₀ ⊆ SC_carrier}
        let E: ss → Set (Set X) := fun s ↦ {e₀: Set X | e₀ ∈ C.sets ∧ e₀ ⊆ (fss s)}
        show SE.Finite
        have SE_decomp : SE = (⋃ s:ss, E s) ∪ {e} := by
            ext e₀
            refine Iff.intro ?mp ?mpr
            case mp =>
                rintro ⟨e₀_in_sets, e₀_sub_SC⟩
                match eq_or_ne e₀ e with
                | Or.inl e₀_eq_e => right; exact e₀_eq_e
                | Or.inr e₀_ne_e =>
                    rcases aux_sub_some_fss e₀_in_sets e₀_sub_SC e₀_ne_e with ⟨s₀, e₀_sub_fss_s₀⟩
                    left
                    simp [E]
                    use e₀_in_sets, s₀, s₀.2
            case mpr =>
                intro he₀
                match he₀ with
                | Or.inr mem_singleton =>
                    rw [mem_singleton]
                    use he
                    exact Set.subset_union_right
                | Or.inl mem_iunion =>
                    simp [E] at mem_iunion
                    use mem_iunion.1
                    rcases mem_iunion.2 with ⟨s₀, s₀_in_ss, hs₀⟩
                    trans ((fss ⟨s₀, s₀_in_ss⟩):Set X)
                    . exact hs₀
                    trans (⋃ s:ss, ((fss s):Set X))
                    . exact Set.subset_iUnion_of_subset ⟨s₀, s₀_in_ss⟩ fun ⦃a⦄ a ↦ a
                    exact Set.subset_union_left
        rw [SE_decomp]
        apply Set.Finite.union
        case ht => exact Set.finite_singleton e
        case hs =>
            have : Finite ss := ss_finite
            apply Set.finite_iUnion
            intro s₀
            rw [←finite_sub_cell_complex_iff]
            apply hf_finite
    let SC: SubCellComplex X := {
        carrier := SC_carrier
        cell_closure_incl := SC_carrier_cell_closure_incl
        cell_incl_or_disjoint:= SC_carrier_cell_incl_or_disjoint
    }
    use SC
    constructor
    . rw [finite_sub_cell_complex_iff]
      exact SC_finite
    exact ce_sub_SC
theorem finite_cell_iunion_subset_finite_sub_complex [CW: CWComplexClass X] {SE: Set C.sets} (hSE: SE.Finite) : ∃ SC: (SubCellComplex X), FiniteCellComplex SC ∧ (⋃ e ∈ SE, e.1) ⊆ SC := by
  choose f f_finite f_cover using @cell_colsure_subset_finite_sub_complex X _ _ C CW
  let SC_carrier : Set X := ⋃ e ∈ SE, (f e.1 e.2)
  have SC_carrier_cell_incl_or_disjoint: ∀ e₁ ∈ C.sets, e₁ ⊆ SC_carrier ∨ Disjoint e₁ SC_carrier := by
    intro e₁ e₁_in_sets
    match eq_or_ne (e₁ ∩ SC_carrier) ∅ with
    | Or.inl inter_eq_empty =>
      right
      rwa [Set.disjoint_iff_inter_eq_empty]
    | Or.inr inter_ne_empty =>
      suffices ∃ e' ∈ SE, e₁ ⊆ (f e'.1 e'.2) by
        left
        intro x x_in_e₁
        rw [Set.mem_iUnion₂]
        rcases this with ⟨e', e'_in_SE, e₁_sub_fe'⟩
        use e', e'_in_SE, e₁_sub_fe' x_in_e₁
      rw [←Set.nonempty_iff_ne_empty] at inter_ne_empty
      rcases inter_ne_empty with ⟨x, ⟨x_in_e₁, x_in_SC_carrier⟩⟩
      rw [Set.mem_iUnion₂] at x_in_SC_carrier
      rcases x_in_SC_carrier with ⟨e₂', e₂'_in_SE, x_in_f_e₂⟩
      have : e₁ ⊆ f e₂'.1 e₂'.2 := by
        apply SubCellComplex.subset_of_intersect
        . exact e₁_in_sets
        rw [←Set.nonempty_iff_ne_empty]
        use x
        tauto
      use e₂'
  have aux_subset_some_fe: ∀ e ∈ C.sets, e ⊆ SC_carrier → ∃ e' ∈ SE, e ⊆ (f e'.1 e'.2) := by
    intro e₁ e₁_in_sets e₁_sub_SC
    rcases C.nonempty e₁ e₁_in_sets with ⟨x, hx⟩
    let x_in_SC := e₁_sub_SC hx
    rw [Set.mem_iUnion₂] at x_in_SC
    rcases x_in_SC with ⟨e', e'_in_SE, x_in_fe'⟩
    use e', e'_in_SE
    have e₁_inter_fe'_nonempty : (e₁ ∩ (f e'.1 e'.2)) ≠ ∅ := by
      rw [←Set.nonempty_iff_ne_empty]
      use x
      exact ⟨hx, x_in_fe'⟩
    exact (f e'.1 e'.2).subset_of_intersect e₁_in_sets e₁_inter_fe'_nonempty
  have SC_carrier_cell_closure_incl: ∀ e₁ ∈ C.sets, e₁ ⊆ SC_carrier → (closure e₁) ⊆ SC_carrier := by
    intro e₁ e₁_in_sets e₁_sub_SC
    suffices ∃ e' ∈ SE, e₁ ⊆ (f e'.1 e'.2) by
      rcases this with ⟨e', e'_in_SE, e₁_sub_fe'⟩
      trans ((f e'.1 e'.2):Set X)
      . exact (f e'.1 e'.2).cell_closure_incl _ e₁_in_sets e₁_sub_fe'
      exact Set.subset_iUnion₂_of_subset e' e'_in_SE fun ⦃a⦄ a ↦ a
    apply aux_subset_some_fe _ e₁_in_sets e₁_sub_SC
  have SC_finite : {e: Set X | e ∈ C.sets ∧ e ⊆ SC_carrier}.Finite := by
    let SE₁ := {e: Set X | e ∈ C.sets ∧ e ⊆ SC_carrier}
    show SE₁.Finite
    let E := fun e:C.sets ↦ {e₀: Set X | e₀ ∈ C.sets ∧ e₀ ⊆ (f e.1 e.2)}
    have SE₁_decomp: SE₁ = ⋃ e ∈ SE, E e := by
      ext e₀
      refine Iff.intro ?mp ?mpr
      case mp =>
        rintro ⟨e₀_in_sets, e₀_sub_SC⟩
        rw [Set.mem_iUnion₂]
        rcases aux_subset_some_fe e₀ e₀_in_sets e₀_sub_SC with ⟨e', e'_in_SE, e₀_sub_fe'⟩
        use e', e'_in_SE
        exact ⟨e₀_in_sets, e₀_sub_fe'⟩
      case mpr =>
        intro e₀_sub_iunion₂
        rw [Set.mem_iUnion₂] at e₀_sub_iunion₂
        rcases e₀_sub_iunion₂ with ⟨e', ⟨e'_in_SE, e₀_sub_Ee'⟩⟩
        have e₀_sub_SC: e₀ ⊆ SC_carrier := by
          intro x x_in_e₀
          rw [Set.mem_iUnion₂]
          use e', e'_in_SE
          exact e₀_sub_Ee'.2 x_in_e₀
        exact ⟨e₀_sub_Ee'.1, e₀_sub_SC⟩
    have : ⋃ e ∈ SE, E e = ⋃ e:SE, E e.1 := by
      exact Set.biUnion_eq_iUnion SE fun x h ↦ E x
    rw [SE₁_decomp, this]
    have : Fintype SE := by exact hSE.fintype
    apply Set.finite_iUnion
    rintro ⟨e', e'_in_SE⟩
    rw [←finite_sub_cell_complex_iff]
    apply f_finite
  let SC: SubCellComplex X := {
      carrier := SC_carrier
      cell_closure_incl := SC_carrier_cell_closure_incl
      cell_incl_or_disjoint:= SC_carrier_cell_incl_or_disjoint
  }
  use SC
  constructor
  . rwa [finite_sub_cell_complex_iff]
  show (⋃ e ∈ SE, e.1) ⊆ SC_carrier
  intro x hx
  rw [Set.mem_iUnion₂] at *
  rcases hx with ⟨e', e'_in_SE, x_in_e'1⟩
  use e', e'_in_SE
  apply f_cover
  apply subset_closure
  exact x_in_e'1
theorem subset_discrete_iff_cell_inter_finite [CW: CWComplexClass X] {S: Set X} : (IsClosed S ∧ (DiscreteTopology S)) ↔ ∀ e ∈ C.sets, (S ∩ e).Finite := by
    refine Iff.intro ?mp ?mpr
    case mp =>
        intro hS e e_in_sets
        suffices (S ∩ (closure e)).Finite by
            apply Set.Finite.subset this
            exact Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) subset_closure
        refine IsCompact.finite ?hcompact ?hdiscrete
        case hcompact => exact IsCompact.of_isClosed_subset (cell_compact e e_in_sets) (IsClosed.inter hS.1 isClosed_closure) Set.inter_subset_right
        case hdiscrete => exact DiscreteTopology.of_subset hS.2 Set.inter_subset_left
    case mpr =>
        intro hS
        have aux_closed: ∀ S₀: Set X, (∀ e ∈ C.sets, (S₀ ∩ e).Finite) → IsClosed S₀ := by
            intro S₀ hS₀
            apply closed_crit_of_coeherent CW.coeherent
            rintro _ ⟨e, e_in_sets, rfl⟩
            let g : (closure e) → X := (↑)
            show IsClosed (g ⁻¹' S₀)
            suffices hfinite: (S₀ ∩ closure e).Finite by
                have : g ⁻¹' S₀ = g ⁻¹' (S₀ ∩ closure e) := by
                    rw [Subtype.preimage_coe_eq_preimage_coe_iff]
                    ext x
                    simp
                    exact fun a a_1 ↦ a
                rw [this]
                exact IsClosed.preimage_val (Set.Finite.isClosed hfinite)
            rcases CW.closure_finite e e_in_sets with ⟨ss, ss_sub_sets, ss_finite, ss_cover⟩
            suffices (S₀ ∩ ⋃₀ ss).Finite by
                apply Set.Finite.subset this
                exact Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) ss_cover
            have : S₀ ∩ ⋃₀ ss = ⋃ s ∈ ss, S₀ ∩ s := by
                ext x
                simp
            rw [this]
            exact Set.Finite.biUnion' ss_finite fun i hi ↦ hS₀ i (ss_sub_sets hi)
        have SClosed: IsClosed S := aux_closed S hS
        have SDiscrete: DiscreteTopology S := by
            rw [discreteTopology_iff_forall_isClosed]
            intro s
            let g : S → X := (↑)
            suffices s_in_x_closed : IsClosed (g '' s) by
                have : s = g ⁻¹' (g '' s) := Eq.symm Set.preimage_val_image_val_eq_self
                rw [this]
                exact IsClosed.preimage_val s_in_x_closed
            apply aux_closed
            intro e e_in_sets
            apply Set.Finite.subset (hS e e_in_sets)
            rintro x ⟨⟨b, b_in_s, rfl⟩, x_in_e⟩
            exact ⟨b.2, x_in_e⟩
        tauto

theorem finite_subcomplex_compact {SC: SubCellComplex X} (hSC: FiniteCellComplex SC) : IsCompact (SC: Set X) := by
  let g: SC → X := (↑)
  have iunion_decomp: (SC : Set X) = ⋃ (e:sub_cell_complex_sets SC), closure (g '' e.1) := by
    ext x
    refine Iff.intro ?mp ?mpr
    case mp =>
      intro hx
      rw [Set.mem_iUnion]
      rcases exists_mem_of_cell (⟨x, hx⟩:SC) with ⟨e₀, e₀_in_SC_sets, coe_x_in_e₀⟩
      use ⟨e₀, e₀_in_SC_sets⟩
      have : x ∈ g '' e₀ := by use ⟨x, hx⟩
      apply subset_closure this
    case mpr =>
      intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨⟨e₀', e₀'_in_SC_sets⟩, he₀'⟩
      let e₀ := g '' e₀'
      have : closure e₀ ⊆ SC := by apply SC.cell_closure_incl e₀ e₀'_in_SC_sets (by apply Subtype.coe_image_subset)
      exact this he₀'
  rw [iunion_decomp]
  have : Fintype (sub_cell_complex_sets SC) := Set.Finite.fintype hSC
  apply isCompact_iUnion
  intro e'
  let e := g '' e'
  exact cell_compact (g '' e') e'.2
end

theorem compact_iff_closed_and_subset_finite_sub_complex {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X] {S: Set X} : IsCompact S ↔ IsClosed S ∧ ∃ SC: SubCellComplex X, FiniteCellComplex SC ∧ S ⊆ SC := by
  refine Iff.intro ?mp ?mpr
  case mpr =>
    rintro ⟨SClosed, ⟨SC, SC_finite, S_sub_SC⟩⟩
    exact (finite_subcomplex_compact SC_finite).of_isClosed_subset SClosed S_sub_SC
  case mp =>
    intro hS
    suffices ∃ SC:SubCellComplex X, FiniteCellComplex SC ∧ S ⊆ SC by
      constructor
      . exact IsCompact.isClosed hS
      exact this
    let SE : Set C.sets := {e | (e.1 ∩ S).Nonempty}
    have SE_iunion_cover : S ⊆ ⋃ e ∈ SE, e.1 := by
      intro x x_in_S
      rw [Set.mem_iUnion₂]
      rcases exists_mem_of_cell x with ⟨e₀, e₀_in_sets, x_in_e₀⟩
      let e₀' : C.sets := ⟨e₀, e₀_in_sets⟩
      have :e₀' ∈ SE := by
        use x
        exact ⟨x_in_e₀, x_in_S⟩
      use e₀', this
    have SE_finite : SE.Finite := by
      have : ∀ e':SE, ∃ x: X, x ∈ e'.1.1 ∩ S := fun e' ↦ e'.2
      choose f hf using this
      have f_inj : Function.Injective f := by
        intro e₁' e₂' heq
        suffices e₁'.1.1 = e₂'.1.1 by
          exact SetCoe.ext (SetCoe.ext this)
        let x := f e₁'
        have mem1 : x ∈ e₁'.1.1 := (hf e₁').1
        have mem2 : x ∈ e₂'.1.1 := by
          simp only [x, heq]
          exact (hf e₂').1
        exact same_cell_of_mem e₁'.1.2 e₂'.1.2 mem1 mem2
      let T := Set.range f
      have T_sub_S : T ⊆ S := by
        rintro x ⟨e', rfl⟩
        exact (hf e').2
      suffices T.Finite by
        rw [←Set.finite_coe_iff]
        have : Finite T := this
        apply Finite.of_injective_finite_range f_inj
      suffices (IsClosed T) ∧ DiscreteTopology T by
        have T_compact: IsCompact T := by
          apply hS.of_isClosed_subset this.1 T_sub_S
        apply T_compact.finite this.2
      rw [subset_discrete_iff_cell_inter_finite]
      intro e e_in_sets
      let e' : C.sets := ⟨e, e_in_sets⟩
      match Classical.em (e' ∈ SE) with
      | Or.inl e'_in_SE =>
        have : (T ∩ e) = {f ⟨e', e'_in_SE⟩} := by
          ext x
          refine Iff.intro ?mp ?mpr
          case mp =>
            intro hx
            rcases hx.1 with ⟨e₀', he₀'⟩
            have x_in_e₀: x ∈ e₀'.1.1 := by
              rw [←he₀']
              exact (hf e₀').1
            have heq: e₀'.1.1 = e := same_cell_of_mem e₀'.1.2 e_in_sets x_in_e₀ hx.2
            have heq': e₀' = ⟨e', e'_in_SE⟩ := by
              apply SetCoe.ext
              apply SetCoe.ext
              exact heq
            rw [←heq']
            exact he₀'.symm
          case mpr =>
            intro hx
            rw [hx]
            constructor
            . use ⟨e', e'_in_SE⟩
            exact (hf ⟨e', e'_in_SE⟩).1
        rw [this]
        exact Set.finite_singleton (f ⟨e', e'_in_SE⟩)
      | Or.inr e'_not_in_SE =>
        have : T ∩ e = ∅ := by
          rw [←Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
          rintro x ⟨⟨e₀', e₀'_in_SE⟩, he'⟩
          have e_ne_e₀ : e ≠ e₀'.1 := by
            contrapose! e'_not_in_SE
            have : e' = e₀' := SetCoe.ext e'_not_in_SE
            rwa [this]
          have e_e₀_disjoint: Disjoint e e₀'.1 := C.disjoint e_in_sets e₀'.2 e_ne_e₀
          rw [Set.disjoint_right] at e_e₀_disjoint
          apply e_e₀_disjoint
          rw [←he']
          exact (hf ⟨e₀', e₀'_in_SE⟩).1
        rw [this]
        exact Set.finite_empty
    rcases finite_cell_iunion_subset_finite_sub_complex SE_finite with ⟨SC, SC_finite, SC_cover⟩
    use SC, SC_finite
    trans ⋃ e ∈ SE, e.1
    . exact SE_iunion_cover
    exact SC_cover

theorem compact_space_iff_finite {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X] : CompactSpace X ↔ FiniteCellComplex X := by
  rw [←isCompact_univ_iff, compact_iff_closed_and_subset_finite_sub_complex]
  simp
  refine Iff.intro ?mp ?mpr
  case mp =>
    rintro ⟨SC, SC_finite, SC_eq_univ⟩
    rw [finite_sub_cell_complex_iff, SC_eq_univ] at SC_finite
    simp at SC_finite
    exact SC_finite
  case mpr =>
    intro sets_finite
    let SC_carrier : Set X := Set.univ
    let SC: SubCellComplex X := {
      carrier := Set.univ
      cell_closure_incl := by simp
      cell_incl_or_disjoint := by simp
    }
    use SC
    constructor
    . rw [finite_sub_cell_complex_iff]
      have : (SC:(Set X)) = Set.univ := rfl
      rw [this]
      simp
      exact sets_finite
    rfl

-- note the locally compact in text is actually WeaklyCompact in Matlib
theorem cw_locally_finite_iff_locally_compact {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X] : (LocallyFinite fun s:C.sets ↦ s.1) ↔ WeaklyLocallyCompactSpace X := by
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro h_locally_finite
    have target: ∀ x:X, ∃ s, IsCompact s ∧ s ∈ 𝓝 x := by
      intro x
      rcases h_locally_finite x with ⟨nx, nx_in_nhds, h_sets_inter_nx_finite⟩
      simp at h_sets_inter_nx_finite
      let SE := {E:C.sets | (E.1 ∩ nx).Nonempty}
      have SE_finite : SE.Finite := h_sets_inter_nx_finite
      -- we have SE being a finite sets
      rcases finite_cell_iunion_subset_finite_sub_complex SE_finite with ⟨SC, SC_finite, SC_cover_iunion⟩
      use (closure nx)
      have cnx_in_nhds: (closure nx) ∈ 𝓝 x := by
        apply (𝓝 x).sets_of_superset nx_in_nhds
        apply subset_closure
      have cnx_compact: IsCompact (closure nx) := by
        rw [compact_iff_closed_and_subset_finite_sub_complex]
        constructor
        . exact isClosed_closure
        use SC, SC_finite
        let uc := ⋃ e ∈ SE, (closure e.1)
        have uc_closed: IsClosed uc := by
          apply Set.Finite.isClosed_biUnion SE_finite
          exact fun i a ↦ isClosed_closure
        trans uc
        . rw [IsClosed.closure_subset_iff uc_closed]
          calc
            nx ⊆ ⋃ e ∈ SE, e.1 := by
              intro x₀ x₀_in_nx
              rw [Set.mem_iUnion₂]
              rcases exists_mem_of_cell x₀ with ⟨e, e_in_sets, x₀_in_e⟩
              use ⟨e, e_in_sets⟩, ⟨x₀, ⟨x₀_in_e, x₀_in_nx⟩⟩
            _ ⊆ uc := by
              apply Set.iUnion₂_mono
              intro e' e'_in_SE
              exact subset_closure
        apply Set.iUnion₂_subset
        intro e' e'_in_SE
        apply SC.cell_closure_incl e'.1 e'.2
        trans ⋃ e ∈ SE, e
        . apply Set.subset_iUnion₂ e' e'_in_SE
        exact SC_cover_iunion
      tauto
    exact { exists_compact_mem_nhds := target }
  case mpr =>
    intro h_local_compact
    intro x
    dsimp
    rcases h_local_compact.exists_compact_mem_nhds x with ⟨s, s_compact, s_in_nhds⟩
    use s, s_in_nhds
    rw [compact_iff_closed_and_subset_finite_sub_complex] at s_compact
    rcases s_compact with ⟨s_closed, ⟨SC, SC_finite, s_in_SC⟩⟩
    let S1 := {e:C.sets | (e.1 ∩ s).Nonempty}
    let S2 := {e | e ∈ C.sets ∧ e ⊆ SC}
    show S1.Finite
    have aux: ∀ e ∈ S1, e.1 ∈ S2 := by
      rintro e ⟨x₀, hx₀⟩
      constructor
      . exact e.2
      apply SC.subset_of_intersect e.2
      rw [←Set.nonempty_iff_ne_empty]
      use x₀
      exact ⟨hx₀.1, s_in_SC hx₀.2⟩
    let f : S1 → S2 := fun ⟨e, e_in_S1⟩ ↦ ⟨e.1, aux e e_in_S1⟩
    have f_inj: Function.Injective f := by
      intro e1 e2 heq
      simp [f] at heq
      apply SetCoe.ext
      apply SetCoe.ext
      exact heq
    have S2_finite : Finite S2 := by
      rw [finite_sub_cell_complex_iff] at SC_finite
      exact SC_finite
    apply Finite.of_injective f f_inj
end Chp5
section
variable {X Y: Type*} [TopologicalSpace X] [TopologicalSpace Y]
end
-- example of dependent arrow notation
-- constructing function having a desired property (proposition is required in f's input)
example {X: Type*} (p : ℕ → X → Prop) (f0: (n: ℕ) →  (x: X) → p n x → X) (hf0: (n : ℕ) → (x : X) → (h: p n x) → p (n+1) (f0 n x h)) (x₀ : X) (hx₀: p 0 x₀): ∃ f: ℕ → X, ∀ n, p n (f n) := by
  have: ∀ n: ℕ, ∃ x: X, p n x := by
    intro n
    induction' n with n ihn
    case zero => use x₀
    case succ =>
      rcases ihn with ⟨x, hx⟩
      use f0 n x hx
      exact hf0 n x hx
  choose f hf using this
  use f

-- proving a constructed function have the desired property (f's value have the property involving adjacent terms)
example {X: Type*} (p: X → X → Prop) (f0: X → X) (hf0: ∀ x: X, p x (f0 x)) (x0: X): ∃ f: ℕ → X, ∀ n, p (f n) (f (n + 1)) := by
  set f : ℕ → X := by
    intro n
    induction' n with n ihn
    case zero => exact x0
    case succ => exact f0 ihn
  with f_def
  use f
  intro n
  exact hf0 (f n)


example {X: Type*} {p : X → Prop} {r: X → X → Prop}
  (f: (x: X) → p x → X)
  (hf0: (x: X) → (h: p x) → p (f x h))
  (hf1: (x: X) → (h: p x) → r x (f x h))
  (x₀: X) (h₀: p x₀) :
  ∃ g: ℕ → X, ∀ n: ℕ, p (g n) ∧ r (g n) (g (n + 1)) := by
    let φ : ℕ → Σ x : X, {y: X // p x} := by
      intro n
      induction' n with n ihn
      case zero => exact ⟨x₀, ⟨x₀, h₀⟩⟩
      case succ =>
        rcases ihn with ⟨xₙ, ⟨ _, hₙ⟩⟩
        exact ⟨f xₙ hₙ, ⟨x₀, hf0 xₙ hₙ⟩⟩
    let g : ℕ → X := fun n ↦ (φ n).1
    use g
    intro n
    constructor
    . exact (φ n).2.2
    have : g (n + 1) = f (g n) (φ n).2.2 := by rfl
    rw [this]
    exact hf1 (g n) (φ n).2.2

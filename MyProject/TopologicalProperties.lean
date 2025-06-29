import MyProject.CellComplex
import Mathlib.Topology.Connected.PathConnected
open Topology
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

section topo_prop_helper
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
  have X1'X2'_open_in_Xnp1: IsOpen (g ⁻¹' X1') ∧ IsOpen (g ⁻¹' X2') := by
    have X1'_closed_in_Xnp1 : IsClosed (g ⁻¹' X1') := by
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
      let Y1 := g ⁻¹' X1'
      show IsClosed Y1
      -- note that we implicitly use the fact that Skeleton X (n + 1) is also a CW complex
      apply closed_crit_of_coeherent CWComplexClass.coeherent
      rintro _ ⟨e, e_in_Xnp1_sets, rfl⟩
      let φ : closure e → (Skeleton X (n + 1)) := (↑)
      show IsClosed (φ ⁻¹' Y1)
      let e₀ := g '' e
      have e₀_in_sets : e₀ ∈ C.sets := e_in_Xnp1_sets
      have e₀_sub_Xnp1 : e₀ ⊆ (Skeleton X (n + 1)) := by
        rintro x ⟨y, hy, rfl⟩
        exact Subtype.coe_prop y
      have ce₀_eq_ce_img : closure e₀ = g '' (closure e) := by
        apply IsClosedMap.closure_image_eq_of_continuous
        case f_closed =>
          apply IsClosed.isClosedMap_subtype_val
          apply sub_cw_cell_complex_closed
        case f_cont =>
          exact continuous_subtype_val
      have gφ_range : Set.range (g ∘ φ) = closure e₀ := by
        rw [ce₀_eq_ce_img, Set.range_comp]
        congr!
        exact Subtype.range_coe
      have : φ ⁻¹' Y1 = (g ∘ φ) ⁻¹' X1' := by ext x;exact Set.mem_preimage
      rw [this, ←Set.preimage_inter_range, gφ_range, Set.inter_comm]
      match sub_X1'_or_disjoint e₀ e₀_in_sets e₀_sub_Xnp1 with
      | Or.inl he₀ =>
        rw [he₀, ←gφ_range, Set.preimage_range]
        exact isClosed_univ
      | Or.inr he₀ =>
        rw [he₀]
        exact isClosed_empty
    have X2'_closed_in_Xnp1 : IsClosed (g ⁻¹' X2') := by
      have sub_X2'_or_disjoint: ∀ e ∈ C.sets, e ⊆ (Skeleton X (n + 1)) → ((closure e) ∩ X2' = closure e) ∨ ((closure e) ∩ X2' = ∅) := by
        intro e e_in_sets e_sub_Xnp1
        match aux_sub_only_1 e e_in_sets e_sub_Xnp1 with
        | Or.inr he =>
          left
          rw [Set.inter_eq_left]
          exact he
        | Or.inl he =>
          right
          have :closure e ∩ X2' ⊆ X2' ∩ X1' := by
            rw [Set.inter_comm]
            exact Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) he
          rw [Set.inter_comm X2', X1'X2'_disjoint] at this
          exact Set.subset_eq_empty this rfl
      let Y2 := g ⁻¹' X2'
      show IsClosed Y2
      apply closed_crit_of_coeherent CWComplexClass.coeherent
      rintro _ ⟨e, e_in_Xnp1_sets, rfl⟩
      let φ : closure e → (Skeleton X (n + 1)) := (↑)
      show IsClosed (φ ⁻¹' Y2)
      let e₀ := g '' e
      let e₀ := g '' e
      have e₀_in_sets : e₀ ∈ C.sets := e_in_Xnp1_sets
      have e₀_sub_Xnp1 : e₀ ⊆ (Skeleton X (n + 1)) := by
        rintro x ⟨y, hy, rfl⟩
        exact Subtype.coe_prop y
      have ce₀_eq_ce_img : closure e₀ = g '' (closure e) := by
        apply IsClosedMap.closure_image_eq_of_continuous
        case f_closed =>
          apply IsClosed.isClosedMap_subtype_val
          apply sub_cw_cell_complex_closed
        case f_cont =>
          exact continuous_subtype_val
      have gφ_range : Set.range (g ∘ φ) = closure e₀ := by
        rw [ce₀_eq_ce_img, Set.range_comp]
        congr!
        exact Subtype.range_coe
      have : φ ⁻¹' Y2 = (g ∘ φ) ⁻¹' X2' := by ext x;exact Set.mem_preimage
      rw [this, ←Set.preimage_inter_range, gφ_range, Set.inter_comm]
      match sub_X2'_or_disjoint e₀ e₀_in_sets e₀_sub_Xnp1 with
      | Or.inl he₀ =>
        rw [he₀, ←gφ_range, Set.preimage_range]
        exact isClosed_univ
      | Or.inr he₀ =>
        rw [he₀]
        exact isClosed_empty
    have g_inv_X1'X2'_rel_compl : g ⁻¹' X1' = (g ⁻¹' X2')ᶜ ∧ g ⁻¹' X2' = (g ⁻¹' X1')ᶜ  := by
      have sub_X1'X2'_eq_Xnp1: (g ⁻¹' X1') ∪ (g ⁻¹' X2') = Set.univ := by
        rw [←Set.preimage_union, X1'X2'_eq_Xnp1, ←Set.preimage_range g]
        congr!
        exact Eq.symm Subtype.range_coe
      have sub_X1'X2'_disjoint: (g ⁻¹' X1') ∩ (g ⁻¹' X2') = ∅ := by
        rw  [←Set.preimage_inter, X1'X2'_disjoint]
        rfl
      have : g ⁻¹' X1' = (g ⁻¹' X2')ᶜ := by
        refine Eq.symm (compl_unique ?disj ?union)
        case disj =>
          show (g ⁻¹' X2') ∩ (g ⁻¹' X1') = ∅
          rw [Set.inter_comm]
          exact sub_X1'X2'_disjoint
        case union =>
          show (g ⁻¹' X2') ∪ (g ⁻¹' X1') = Set.univ
          rw [Set.union_comm]
          exact sub_X1'X2'_eq_Xnp1
      constructor
      . exact this
      rw [eq_compl_comm]
      exact this
    have X1'_open_in_Xnp1 : IsOpen (g ⁻¹' X1') := by
      rw [g_inv_X1'X2'_rel_compl.1]
      exact IsClosed.isOpen_compl
    have X2'_open_in_Xnp1 : IsOpen (g ⁻¹' X2') := by
      rw [g_inv_X1'X2'_rel_compl.2]
      exact IsClosed.isOpen_compl
    exact ⟨X1'_open_in_Xnp1, X2'_open_in_Xnp1⟩
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
end topo_prop_helper

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
    rcases le_or_lt m n with m_le_n | n_lt_m
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
    have Z1Closed: IsClosed Z1 := by
      have sub_Z1_or_disjoint: ∀ e ∈ C.sets, (closure e) ∩ Z1 = (closure e) ∨ (closure e) ∩ Z1 = ∅ := by
        intro e e_in_sets
        match aux_ce_sub_only_one e e_in_sets with
        | Or.inl e_sub_Z1 =>
          left
          rw [eq_comm, Set.left_eq_inter]
          exact e_sub_Z1
        | Or.inr e_sub_Z2 =>
          right
          rw [←Set.disjoint_iff_inter_eq_empty, disjoint_comm]
          exact Set.disjoint_of_subset (fun x hx ↦ hx) e_sub_Z2 Z1Z2_disjoint
      apply closed_crit_of_coeherent CWComplexClass.coeherent
      rintro _ ⟨e₀, e₀_in_sets, rfl⟩
      rw [←Set.preimage_inter_range, Subtype.range_val]
      let g : (closure e₀) → X := (↑)
      have ce₀_eq_range : closure e₀ = Set.range g := by
        exact Eq.symm Subtype.range_coe
      show IsClosed (g ⁻¹' (Z1 ∩ closure e₀))
      match sub_Z1_or_disjoint e₀ e₀_in_sets with
      | Or.inl ce₀_in_Z1 =>
        rw [Set.inter_comm, ce₀_in_Z1]
        simp [ce₀_eq_range]
      | Or.inr ce₀_not_in_Z1 =>
        rw [Set.inter_comm, ce₀_not_in_Z1]
        simp
    have Z2Closed: IsClosed Z2 := by
      have sub_Z2_or_disjoint: ∀ e ∈ C.sets, (closure e) ∩ Z2 = (closure e) ∨ (closure e) ∩ Z2 = ∅ := by
        intro e e_in_sets
        match aux_ce_sub_only_one e e_in_sets with
        | Or.inr e_sub_Z2 =>
          left
          rw [eq_comm, Set.left_eq_inter]
          exact e_sub_Z2
        | Or.inl e_sub_Z1 =>
          right
          rw [←Set.disjoint_iff_inter_eq_empty, disjoint_comm]
          exact Set.disjoint_of_subset (fun x hx ↦ hx) e_sub_Z1 Z1Z2_disjoint.symm
      apply closed_crit_of_coeherent CWComplexClass.coeherent
      rintro _ ⟨e₀, e₀_in_sets, rfl⟩
      rw [←Set.preimage_inter_range, Subtype.range_val]
      let g : (closure e₀) → X := (↑)
      have ce₀_eq_range : closure e₀ = Set.range g := by
        exact Eq.symm Subtype.range_coe
      show IsClosed (g ⁻¹' (Z2 ∩ closure e₀))
      match sub_Z2_or_disjoint e₀ e₀_in_sets with
      | Or.inl ce₀_in_Z2 =>
        rw [Set.inter_comm, ce₀_in_Z2]
        simp [ce₀_eq_range]
      | Or.inr ce₀_not_in_Z2 =>
        rw [Set.inter_comm, ce₀_not_in_Z2]
        simp
    have Z1Z2_compl : Z1ᶜ = Z2 := by
      refine compl_unique ?disj ?union
      case disj =>
        show Z1 ∩ Z2 = ∅
        rw [←Set.disjoint_iff_inter_eq_empty]
        exact Z1Z2_disjoint
      case union => exact Z1Z2_cover
    have Z1Open: IsOpen Z1 := by
      rw [←isClosed_compl_iff, Z1Z2_compl]
      exact Z2Closed
    have Z2Open: IsOpen Z2 := by
      rw [← Z1Z2_compl]
      apply IsClosed.isOpen_compl
    tauto
  have univ_preconnected: @IsPreconnected X _ Set.univ := isPreconnected_univ
  have univ_not_preconnected: ¬(@IsPreconnected X _ Set.univ) := by
    simp [IsPreconnected]
    use Z1, Z1Z2Open.1, Z2, Z1Z2Open.2, Z1Z2_cover, Z1_nonempty, Z2_nonempty
    rw [Set.not_nonempty_iff_eq_empty, ←Set.disjoint_iff_inter_eq_empty]
    exact Z1Z2_disjoint
  contradiction

end Chp5

section
variable {X Y: Type*} [TopologicalSpace X] [TopologicalSpace Y]
example {f: X → Y} (hf: IsClosedMap f) (fc: Continuous f) {s: Set X} : f '' (closure s) = closure (f '' s) := by exact Eq.symm (IsClosedMap.closure_image_eq_of_continuous hf fc s)
example {s : Set X} (hs: IsClosed s) : let g : s → X := (↑); IsClosedMap g := by
  exact IsClosed.isClosedMap_subtype_val hs
example {f: X → Y} (t: Set Y) : f ⁻¹' t = f ⁻¹' (t ∩ Set.range f) := by
  exact Eq.symm Set.preimage_inter_range
example {f: X → Y} : f ⁻¹' (Set.range f) = Set.univ := by
  exact Set.preimage_range f
example {s1 s2 : Set X} (h0: s1 ⊆ s2) (h1: IsClosed s2) : closure s1 ⊆ s2 := by
  exact (IsClosed.closure_subset_iff h1).mpr h0
example {s1 s2 s3: Set X} (h0: s1 = s2 ∪ s3) (h1: s2 ∩ s3 = ∅) : s1 \ s2 = s3 := by
  rw [h0]
  apply Set.union_diff_cancel_left ?_
  exact Set.subset_empty_iff.mpr h1
example {s: Set X} : closure s = s ∪ (closure s \ s) := by
  exact Eq.symm (Set.union_diff_cancel' (fun ⦃a⦄ a ↦ a) subset_closure)
example {f: X → Y}: f ⁻¹' ∅ = ∅ := by exact rfl
example {s1 s2 s3: Set X} : s1 ∩ s2 ∩ s3 = (s1 ∩ s3) ∩ s2 := Set.inter_right_comm s1 s2 s3
example (s1 s2 s3: Set X) : (s1 ∩ s3) ∩ (s2 ∩ s3) = (s1 ∩ s2) ∩ s3 := by
  exact Eq.symm (Set.inter_inter_distrib_right s1 s2 s3)
example (s1 s2 s3: Set X) (h23: Disjoint s2 s3) (h112: s1 ⊆ s2) : Disjoint s1 s3 := by
  exact Set.disjoint_of_subset h112 (fun ⦃a⦄ a ↦ a) h23
example (s1 s2 s3: Set X) (h23: Disjoint s2 s3) (h112: s1 ⊆ s3) : Disjoint s2 s1 := by
  exact Set.disjoint_of_subset (fun ⦃a⦄ a ↦ a) h112 h23
example (s1 s2: Set X) (h: ∀ x, x ∈ s1 → x ∉ s2) : Disjoint s1 s2 := by
  exact Set.disjoint_left.mpr h
example (s1 s2: Set X) {x: X} (h1: x ∈ s1) (h2: x ∈ s2) (h: Disjoint s1 s2) : False := by
  apply Set.disjoint_left.mp h h1 h2
example {s1 :Set X} (h: ¬s1.Nonempty) : s1 = ∅ := by
  exact Set.not_nonempty_iff_eq_empty.mp h
#check Path
#check IsPathConnected.union
example {ι : Type*} {f: ι → Set X} {s₀: Set X} (i₀: ι) (hs₀: s₀.Nonempty) (hf_pc: ∀ i:ι, IsPathConnected (f i)) (hf_incl: ∀ i:ι, s₀ ⊆ f i) : IsPathConnected (⋃ i:ι, f i) := by
  rcases hs₀ with ⟨x, hx⟩
  have : x ∈ ⋃ i:ι, f i := by
    rw [Set.mem_iUnion]
    use i₀
    exact hf_incl i₀ hx
  use x, this
  intro y hy
  rw [Set.mem_iUnion] at hy
  rcases hy with ⟨i₁, y_in_fi₁⟩
  exact ((hf_pc i₁).joinedIn x (hf_incl i₁ hx) y y_in_fi₁).mono (Set.subset_iUnion f i₁)
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

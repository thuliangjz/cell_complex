import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Constructions
import Mathlib.Analysis.NormedSpace.Connected

namespace Chp5
def b := fun n ↦ Metric.ball (0: EuclideanSpace ℝ (Fin n)) 1
def cb := fun n ↦ Metric.closedBall (0: EuclideanSpace ℝ (Fin n)) 1
def sph := fun n ↦ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-
    EuclideanSpace ℝ (Fin n) is actually a ProperSpace where every closed ball is compact
-/
example {n : ℕ} : IsCompact (cb n) := by
    rw [cb]
    apply isCompact_closedBall
instance cb_compact {n : ℕ} : CompactSpace (cb n) := by
    exact isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
instance sph_connected {n : ℕ} (hn: 1 < n) : ConnectedSpace (sph n) := by
    apply isConnected_iff_connectedSpace.mp
    apply isConnected_sphere
    case h =>
        have : Module.rank ℝ (EuclideanSpace ℝ (Fin n)) = n := by apply rank_fin_fun
        rw [this]
        exact Nat.one_lt_cast.mpr hn
    case hr=>
        norm_num
theorem sph_nonempty {n : ℕ} (hn: 1 ≤ n) : (sph n).Nonempty := by
    have : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
        rw [nontrivial_iff]
        use EuclideanSpace.single (⟨0, hn⟩) (1:ℝ), 0
        by_contra! eq_zero
        rw [EuclideanSpace.single_eq_zero_iff] at eq_zero
        linarith
    rw [sph, NormedSpace.sphere_nonempty]
    norm_num
theorem b_closure_eq_cb {n : ℕ} : closure (b n) = cb n := by
    rw [b, cb]
    refine closure_ball 0 ?_
    norm_num
instance cb_connected {n : ℕ} : ConnectedSpace (cb n) := by
    apply isConnected_iff_connectedSpace.mp
    rw [←b_closure_eq_cb]
    apply IsConnected.closure
    apply Metric.isConnected_ball
    norm_num
theorem cb_contractible {n : ℕ} : ContractibleSpace (cb n) := by
    apply Convex.contractibleSpace
    apply convex_closedBall
    use 0
    rw [cb, Metric.mem_closedBall]
    norm_num
theorem cb_path_connected {n : ℕ} : PathConnectedSpace (cb n) := by
    exact @ContractibleSpace.instPathConnectedSpace _ _ (cb_contractible)
theorem b_in_cb {n : ℕ}: b n ⊆ cb n := by
    intro x
    rw [b, cb, Metric.mem_ball, Metric.mem_closedBall]
    apply le_of_lt
theorem sph_in_cb {n : ℕ} : sph n ⊆ cb n := by
    intro x
    rw [sph, cb, Metric.mem_sphere, Metric.mem_closedBall]
    apply le_of_eq
def cb_inner_map {n : ℕ} {X: Type*} (f: cb n → X) : (b n → X) := by
    intro x
    exact f ⟨x.val, b_in_cb x.prop⟩
def cb_boundary_map {n : ℕ} {X : Type*} (f: cb n → X) : (sph n → X) := by
    intro x
    exact f ⟨x.val, sph_in_cb x.prop⟩
@[simp]
def b_to_cb {n : ℕ} : (b n) → (cb n) := fun x ↦ ⟨x.val, b_in_cb x.prop⟩

def cb_inner {n : ℕ} : Set (cb n) := Set.range b_to_cb
@[simp]
def sph_to_cb {n : ℕ} : (sph n) → (cb n) := fun x ↦ ⟨x.val, sph_in_cb x.prop⟩

def cb_boundary {n : ℕ} : Set (cb n) := Set.range sph_to_cb
theorem inner_map_eq_comp {n: ℕ} {X: Type*} (f: cb n → X) : cb_inner_map f = f ∘ b_to_cb := rfl
theorem inner_map_range {n : ℕ} {X: Type*} (f : cb n → X) : Set.range (cb_inner_map f) = f '' cb_inner := by
    have : cb_inner_map f = f ∘ b_to_cb := by
        ext x
        simp [cb_inner_map, b_to_cb]
    rw [this, cb_inner]
    exact Set.range_comp f b_to_cb

theorem inner_map_comp {n: ℕ} {X Y: Type*} (f: cb n → X) (g: X → Y) : cb_inner_map (g ∘ f) = g ∘ (cb_inner_map f) := by
    ext x
    simp [cb_inner_map]

theorem boundary_map_comp {n: ℕ} {X Y: Type*} (f: cb n → X) (g: X → Y): cb_boundary_map (g ∘ f) = g ∘ (cb_boundary_map f) := by
    ext x
    simp [cb_boundary_map]

theorem mem_boundary_map_range_of_mem_boundary {n : ℕ} {X: Type*} (f : cb n → X) {y : cb n} (hy: y ∈ cb_boundary) : f y ∈ Set.range (cb_boundary_map f) := by
    rcases hy with⟨z, hz⟩
    use z
    rw [sph_to_cb] at hz
    rw [cb_boundary_map, hz]

theorem boundary_map_range {n : ℕ} {X: Type*} (f : cb n → X) : Set.range (cb_boundary_map f) = f '' cb_boundary := by
    have : cb_boundary_map f = f ∘ sph_to_cb := by
        ext x
        simp [cb_boundary_map]
    rw [this, cb_boundary]
    apply Set.range_comp

theorem mem_cb_inner_or_boundary {n : ℕ} (y : cb n) : y ∈ cb_inner ∨ y ∈ cb_boundary := by
    have hy : y.val ∈ Metric.closedBall 0 1 := y.prop
    rw [Metric.mem_closedBall] at hy
    rcases lt_or_eq_of_le hy with hy | hy
    . rw [←Metric.mem_ball] at hy
      left
      use ⟨y.val, hy⟩
      simp
    . rw [←Metric.mem_sphere] at hy
      right
      use ⟨y.val, hy⟩
      simp

theorem cb_map_range_decomposition {n: ℕ} {X: Type*} (f: cb n → X) : Set.range f = (Set.range (cb_boundary_map f)) ∪ (Set.range (cb_inner_map f)) := by
    rw [boundary_map_range, inner_map_range]
    ext y
    constructor
    case mp =>
        rintro ⟨x, hx, rfl⟩
        match mem_cb_inner_or_boundary x with
        | Or.inl h =>
            right
            use x
        | Or.inr h =>
            left
            use x
    case mpr =>
        intro hy
        match hy with
        | Or.inl h =>
            exact Set.mem_range_of_mem_image f cb_boundary h
        | Or.inr h =>
            exact Set.mem_range_of_mem_image f cb_inner h

theorem cb_inner_closure {n : ℕ} : closure (@cb_inner n) = Set.univ := by
    let f := fun x : cb n ↦ x.val
    have ce: Topology.IsClosedEmbedding f := by exact Isometry.isClosedEmbedding fun x1 ↦ congrFun rfl
    have h: f '' (closure cb_inner) = closure (f '' cb_inner) := by rw [Topology.IsClosedEmbedding.closure_image_eq ce cb_inner]
    have closure_img_eq_cb : closure (f '' cb_inner) = cb n := by
        have : f '' cb_inner = b n := by
            ext x
            simp [f, cb_inner, b_to_cb]
            apply b_in_cb
        rw [this]
        apply b_closure_eq_cb
    rw [closure_img_eq_cb] at h
    calc
        closure cb_inner = f ⁻¹' (f '' closure cb_inner) := by rw[Set.preimage_val_image_val_eq_self]
        _                = Set.univ := by rw [h]; ext x; simp [f]
theorem cb_inner_open {n : ℕ} : IsOpen (@cb_inner n) := by
    set f := fun x : cb n ↦ x.val with f_def
    have f_embed : Topology.IsEmbedding f := by exact Topology.IsEmbedding.subtypeVal
    show ∃ s, IsOpen s ∧ f ⁻¹' s = cb_inner
    use b n
    constructor
    . apply Metric.isOpen_ball
    ext x
    simp [cb_inner, b_to_cb]
    constructor
    . intro h
      use x, h
    rintro ⟨x1, ⟨hx1, rfl⟩⟩
    exact hx1

theorem cb_boundary_inner_cmpl {n : ℕ} : Set.univ \ @cb_inner n = cb_boundary := by
    ext y
    constructor
    case mp =>
        intro hy
        have : y ∈ cb_inner ∨ y ∈ cb_boundary := by exact mem_cb_inner_or_boundary y
        simp at hy
        tauto
    case mpr =>
        intro hy
        simp
        by_contra! hy'
        have : dist 0 y.val = 1 := by
            rw [cb_boundary] at hy
            rcases hy with ⟨x, hx⟩
            rw [sph_to_cb] at hx
            simp [←hx]
        have : dist 0 y.val < 1 := by
            rw [cb_inner] at hy'
            rcases hy' with ⟨x, hx⟩
            rw [b_to_cb] at hx
            rw [←hx, dist_comm, ←Metric.mem_ball]
            simp
        linarith

theorem cb_boundary_eq_inner_compl {n: ℕ}: @cb_boundary n = cb_innerᶜ := by
  ext x
  simp [←cb_boundary_inner_cmpl]

theorem cb_inner_eq_boundary_compl {n: ℕ}: @cb_inner n = cb_boundaryᶜ := by
  ext x
  simp [←cb_boundary_inner_cmpl]

theorem cb_boundary_closed {n: ℕ}: IsClosed (@cb_boundary n) := by
  rw [←cb_boundary_inner_cmpl, ←Set.compl_eq_univ_diff, isClosed_compl_iff]
  exact cb_inner_open

theorem cb_boundary_connected {n: ℕ} (hn: 1 < n) : IsConnected (@cb_boundary n) := by
    rw [cb_boundary,←Set.image_univ]
    apply IsConnected.image
    case H =>
        refine connectedSpace_iff_univ.mp ?_
        exact sph_connected hn
    case hf =>
        refine continuous_iff_continuousOn_univ.mp ?_
        exact Isometry.continuous fun x1 ↦ congrFun rfl

theorem cb_decomp {n: ℕ} {x: cb n} : x ∈ cb_inner ∨ x ∈ cb_boundary := by
  rcases Classical.em (x ∈ cb_inner) with x_in_cb_inner | x_not_in_cb_inner
  . left
    exact x_in_cb_inner
  right
  rw [←cb_boundary_inner_cmpl]
  simpa using x_not_in_cb_inner
theorem b_to_cb_cont {n: ℕ} : Continuous (@b_to_cb n) := by
  exact Isometry.continuous fun x1 ↦ congrFun rfl

theorem b_to_cb_inducing {n: ℕ}: Topology.IsInducing (@b_to_cb n) := by
  refine { eq_induced := ?_ }
  ext s
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro hs
    have s_open_in_Rn: IsOpen (Subtype.val '' s) := by
      refine IsOpen.trans hs ?_
      rw [b]
      exact Metric.isOpen_ball
    have s_open_in_cb: IsOpen ((Subtype.val: cb (n) → EuclideanSpace ℝ (Fin n)) ⁻¹' (Subtype.val '' s)) := by
      exact IsOpen.preimage_val s_open_in_Rn
    use (Subtype.val: cb (n) → EuclideanSpace ℝ (Fin n)) ⁻¹' (Subtype.val '' s), s_open_in_cb
    ext x
    simp
  case mpr =>
    rintro ⟨t, ⟨u, u_open_in_Rn, rfl⟩, rfl⟩
    exact isOpen_induced u_open_in_Rn

theorem b_to_cb_open_map {n: ℕ}: IsOpenMap (@b_to_cb n) := by
  intro s hs
  have s_open_in_Rn: IsOpen (Subtype.val '' s) := by
      refine IsOpen.trans hs ?_
      rw [b]
      exact Metric.isOpen_ball
  use (Subtype.val '' s), s_open_in_Rn
  ext x
  refine Iff.intro ?mp ?mpr
  case mp =>
    rintro ⟨y, y_in_s, heq⟩
    use y, y_in_s
    exact SetCoe.ext heq
  case mpr =>
    rintro ⟨y, y_in_s, rfl⟩
    simp [y_in_s]

--theorem cb_singleton : cb 0 = {0} := by
--    exact Eq.symm (Set.eq_of_nonempty_of_subsingleton {0} (cb 0))

instance : Subsingleton (cb 0) := by
    exact Set.subsingleton_coe_of_subsingleton

instance : Subsingleton (b 0) := by
    exact Set.subsingleton_coe_of_subsingleton

theorem zero_in_b {n: ℕ}: 0 ∈ b n := by
  rw [b, Metric.mem_ball]
  norm_num

theorem zero_in_cb {n: ℕ}: 0 ∈ cb n:= by
  apply b_in_cb
  exact zero_in_b

theorem zero_in_cb_inner {n: ℕ}: ⟨0, zero_in_cb⟩ ∈ @cb_inner n := by
  rw [cb_inner]
  use ⟨0, zero_in_b⟩
  rfl

instance {n: ℕ} : Inhabited (cb n) := by
    use 0
    exact zero_in_cb

instance {n: ℕ} : Inhabited (b n) := by
    use 0
    exact zero_in_b

theorem b0_singleton : b 0 = {0} := by
    simp [b]
    refine Metric.ball_eq_singleton_of_subsingleton ?_
    norm_num

theorem b_singleton_iff : ∀ n : ℕ, (∃ x, b n = {x}) ↔ n = 0 := by
    intro n
    refine Iff.intro ?mp ?mpr
    case mp =>
        rintro ⟨x, hx⟩
        by_contra! n_ne_0
        have n_gt_0 : 0 < n := Nat.zero_lt_of_ne_zero n_ne_0
        have x_eq_zero: x = 0 := by
            have aux: 0 ∈ b n := by
                rw [b, Metric.mem_ball]
                norm_num
            rw [hx] at aux
            exact Eq.symm aux
        let x₀ := EuclideanSpace.single (⟨0, n_gt_0⟩:Fin n) ((1:ℝ)/2)
        have x_eq_x₀ : x = x₀ := by
            have aux: x₀ ∈ b n := by
                rw [b, Metric.mem_ball]
                simp [x₀]
                exact two_inv_lt_one
            rw [hx] at aux
            exact Eq.symm aux
        have x₀_eq_0 : x₀ = 0 := by
            trans x
            exact Eq.symm x_eq_x₀
            exact x_eq_zero
        rw [EuclideanSpace.single_eq_zero_iff] at x₀_eq_0
        have : (1:ℝ) / 2 ≠ 0 := by
            refine one_div_ne_zero ?_
            exact Ne.symm (NeZero.ne' 2)
        exact this x₀_eq_0
    case mpr =>
        intro hn
        rw [hn]
        use 0
        apply b0_singleton

theorem sph0_empty: sph 0 = ∅ := by
  rw [sph]
  apply Metric.sphere_eq_empty_of_subsingleton ?_
  norm_num

theorem cb0_boundary_empty: @cb_boundary 0 = ∅ := by
  rw [cb_boundary, Set.range_eq_empty_iff, Set.isEmpty_coe_sort]
  exact sph0_empty

section
variable {X: Type*} [TopologicalSpace X]
theorem closure_decomposition {A: Set X} : closure A = frontier A ∪ interior A := by
  unfold frontier
  refine Eq.symm (Set.diff_union_of_subset ?_)
  exact interior_subset_closure
end

section
variable {n: ℕ}

def f_ray (p x: EuclideanSpace ℝ (Fin n)): ℝ → (EuclideanSpace ℝ (Fin n)) := fun t ↦ p + t • (x - p)

def seg_inside (p x: EuclideanSpace ℝ (Fin n)) (A: Set (EuclideanSpace ℝ (Fin n))): Set ℝ := (f_ray p x) ⁻¹' A

noncomputable def sep_fun (p: EuclideanSpace ℝ (Fin n)) (A: Set (EuclideanSpace ℝ (Fin n))): EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ if x = p then 0 else 1 / sSup (seg_inside p x A)

theorem f_ray_cont (p x: EuclideanSpace ℝ (Fin n)): Continuous (f_ray p x) := by
  unfold f_ray
  continuity

lemma f_ray_on_cont_prop {p x: EuclideanSpace ℝ (Fin n)} {Pp: EuclideanSpace ℝ (Fin n) → Prop} (hPp: ∀ x, Pp x → ∃ d > 0, ∀ y ∈ Metric.ball x d, Pp y) {t: ℝ} (ht_nz: t ≠ 0) (hft: Pp (f_ray p x t)) : ∃ d > 0, ∀ y, dist x y < d → Pp (f_ray p y t) := by
  rcases hPp _ hft with ⟨δ, δpos, hδ⟩
  let d := δ / |t|
  have dpos: d > 0 := div_pos δpos (abs_pos.mpr ht_nz)
  use d, dpos
  intro y hy
  apply hδ
  rw [Metric.mem_ball]
  show ‖(f_ray p y t) - (f_ray p x t)‖ < δ
  simp [f_ray, ←smul_sub, norm_smul, ←lt_div_iff₀' (abs_pos.mpr ht_nz)]
  rw [dist_comm] at hy
  exact hy

lemma f_ray_interior_of_interior_endpoint {p x: EuclideanSpace ℝ (Fin n)} {A: Set (EuclideanSpace ℝ (Fin n))}
  (hA: Convex ℝ A) (hp: p ∈ interior A) (hx: x ∈ A): ∀ t ∈ Set.Ico (0:ℝ) 1, (f_ray p x t) ∈ interior A := by
  intro t ht
  rw [Set.mem_Ico] at ht
  rcases eq_or_ne p x with p_eq_x | p_ne_x
  . simpa [f_ray, ←p_eq_x]
  . rcases Metric.mem_nhds_iff.mp (IsOpen.mem_nhds isOpen_interior hp) with ⟨δ, δpos, hδ⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    let d := (1 - t) * δ
    have dpos: d > 0 := by
      refine mul_pos ?_ δpos
      linarith
    use d, dpos
    intro y hy
    let y' := x + (1 / (1 - t)) • (y - x)
    have one_minus_t_ne_zero: 1 - t ≠ 0 := by linarith
    have one_minus_t_gt_zero: 1 - t > 0 := by linarith
    have y'_in_A: y' ∈ A := by
      apply interior_subset
      apply hδ
      rw [Metric.mem_ball]
      show ‖y' - p‖ < δ
      calc
        ‖y' - p‖ = ‖x + (1 / (1 - t)) • (y - x) - p‖ := rfl
        _ = ‖x + (1 / (1 - t)) • (((f_ray p x t) - x) + (y - (f_ray p x t))) - p‖ := by simp
        _ = ‖(x - p) + (1 / (1 - t)) • ((f_ray p x t) - x) + (1 / (1 - t)) • (y - (f_ray p x t))‖ := by congr! 1; module
        _ = ‖(x - p) + (1 / (1 - t)) • ((p + t • (x - p)) - x) + (1 / (1 - t)) • (y - (f_ray p x t))‖ := by rfl
        _ = ‖(x - p) + (1 / (1 - t) * (1 - t)) • (p - x) + (1 / (1 - t)) • (y - (f_ray p x t))‖ := by congr! 1; module
        _ = ‖(x - p) + (1:ℝ) • (p - x) + (1 / (1 - t)) • (y - (f_ray p x t))‖ := by
          congr;
          field_simp
        _ = ‖(1 / (1 - t)) • (y - (f_ray p x t))‖ := by congr! 1; module
        _ < δ := by
          rw [norm_smul]
          field_simp
          rw [abs_of_pos one_minus_t_gt_zero, (div_lt_iff₀' one_minus_t_gt_zero)]
          rw [Metric.mem_ball] at hy
          exact hy
    have y_eq_combination: y = t • x + (1 - t) • y' := by
      unfold y'
      match_scalars
      . field_simp
      . field_simp; ring
    rw [y_eq_combination]
    apply hA hx y'_in_A ht.1 (by linarith) (by ring)

-- actually we proved a special case for the following theorem
#check Convex.add_smul_mem_interior

lemma seg_inside_nonempty (p x: EuclideanSpace ℝ (Fin n)) (A: Set (EuclideanSpace ℝ (Fin n))) (hx: x ∈ A): (seg_inside p x A).Nonempty := by
  use 1
  simp [seg_inside, f_ray]
  exact hx

lemma seg_inside_bdd (p x: EuclideanSpace ℝ (Fin n)) (A: Set (EuclideanSpace ℝ (Fin n))) (hA: IsCompact A) (hxp: x ≠ p): BddAbove (seg_inside p x A) := by
  have nxp_gt_0 : ‖x - p‖ > 0 := norm_sub_pos_iff.mpr hxp
  rcases hA.isBounded.subset_closedBall p with ⟨r, hr⟩
  use r / ‖x - p‖
  simp [upperBounds, seg_inside]
  intro t ht
  unfold f_ray at ht
  let ht' := hr ht
  simp [norm_smul] at ht'
  rw [le_div_iff₀ nxp_gt_0]
  trans |t| * ‖x - p‖
  . rw [mul_le_mul_iff_of_pos_right nxp_gt_0]
    exact le_abs_self t
  . exact ht'

lemma seg_inside_has_lub (p x: EuclideanSpace ℝ (Fin n)) (A: Set (EuclideanSpace ℝ (Fin n))) (hA: IsCompact A) (hxp: x ≠ p) (hx: x ∈ A): IsLUB (seg_inside p x A) (sSup (seg_inside p x A)) := by
  refine isLUB_csSup ?_ ?_
  . exact seg_inside_nonempty p x A hx
  . exact seg_inside_bdd p x A hA hxp

lemma seg_inside_sup_pos (p x: EuclideanSpace ℝ (Fin n)) (A: Set (EuclideanSpace ℝ (Fin n))) (hA: IsCompact A) (hxp: x ≠ p) (hx: x ∈ A) : (sSup (seg_inside p x A)) > 0 := by
  apply lt_of_lt_of_le (b := 1)
  . norm_num
  apply le_csSup (seg_inside_bdd p x A hA hxp)
  simpa [seg_inside, f_ray]

lemma seg_inside_sup_pos_of_interior (p x: EuclideanSpace ℝ (Fin n)) (A: Set (EuclideanSpace ℝ (Fin n))) (hA: IsCompact A) (hxp: x ≠ p) (hp: p ∈ interior A): (sSup (seg_inside p x A)) > 0 := by
  have int_A_is_p_nhds: interior A ∈ nhds p := by
    rw [mem_nhds_iff]
    use interior A, (fun a ah ↦ ah), isOpen_interior
  rw [Metric.mem_nhds_iff] at int_A_is_p_nhds
  rcases int_A_is_p_nhds with ⟨δ, δpos, hδ⟩
  let d := δ / (2 * dist x p)
  have dpos: d > 0 := by
    apply div_pos δpos
    suffices dist x p > 0 by
      linarith
    exact dist_pos.mpr hxp
  have d_in_seg_inside: d ∈ seg_inside p x A := by
    apply interior_subset (s:=A)
    apply hδ
    simp [Metric.mem_ball, f_ray, norm_smul]
    calc
      |d| * ‖x - p‖ = |(δ / (2 * ‖x - p‖))| * ‖x - p‖ := rfl
      _ = |δ| / |2 * ‖x - p‖| * ‖x - p‖ := by rw[abs_div]
      _ = |δ| / (2 * ‖x - p‖) * ‖x - p‖ := by rw [abs_mul]; simp
      _ = |δ| / 2 := by have: ‖x - p‖ ≠ 0 := ne_of_gt (dist_pos.mpr hxp); field_simp; ring
      _ < δ := by rw [abs_of_pos δpos]; exact div_two_lt_of_pos δpos
  apply lt_of_lt_of_le (b := d)
  . exact dpos
  . exact le_csSup (seg_inside_bdd p x A hA hxp) d_in_seg_inside

lemma nonempty_frontier_of_compact_nonempty_subset {A: Set (EuclideanSpace ℝ (Fin n))} (hn: n > 0) (h_A_compact: IsCompact A) (h_A_nonempty: A.Nonempty): (frontier A).Nonempty := by
  by_contra! frontier_empty
  have A_closed: IsClosed A := IsCompact.isClosed h_A_compact
  have A_eq_interior: A = interior A := by
    nth_rw 1 [A_closed.closure_eq.symm]
    rw [closure_decomposition, frontier_empty]
    simp
  have A_open: IsOpen A := interior_eq_iff_isOpen.mp (id (Eq.symm A_eq_interior))
  have A_compl_nonempty: (Aᶜ).Nonempty := by
    rw [Set.nonempty_def]
    rcases h_A_compact.isBounded.subset_closedBall 0 with ⟨r, hr⟩
    have r_noneg: r ≥ 0 := by
      have cb_nonempty: (Metric.closedBall (0: EuclideanSpace ℝ (Fin n)) r).Nonempty := by
        rcases h_A_nonempty with ⟨p, p_in_A⟩
        use p
        exact hr p_in_A
      exact Metric.nonempty_closedBall.mp cb_nonempty
    use (r + 1) • (EuclideanSpace.single ⟨0, hn⟩ 1)
    by_contra! not_mem_compl
    simp at not_mem_compl
    let mem_closed_ball := hr not_mem_compl
    simp [Metric.mem_closedBall, dist_eq_norm, norm_smul] at mem_closed_ball
    have : |r + 1|= r + 1 := by apply abs_of_nonneg; linarith
    rw [this] at mem_closed_ball
    linarith
  have A_compl_open: IsOpen Aᶜ := by exact IsClosed.isOpen_compl
  have univ_sub_union: Set.univ ⊆ A ∪ Aᶜ := by intro x; simp
  have univ_preconnected: IsPreconnected (Set.univ: Set (EuclideanSpace ℝ (Fin n))) := isPreconnected_univ
  have inter_nonempty: (A ∩ Aᶜ).Nonempty := by simpa using (univ_preconnected A Aᶜ A_open A_compl_open univ_sub_union (by simpa) (by simpa))
  simp at inter_nonempty
open Topology
lemma interior_boundary_min_dist {p: EuclideanSpace ℝ (Fin n)} {A: Set (EuclideanSpace ℝ (Fin n))} (hn: n > 0) (h_A_compact: IsCompact A) (hp: p ∈ interior A): ∃ d > (0:ℝ), ∀ x ∈ A, x ≠ p → d ≤ sSup (seg_inside p x A) * ‖x - p‖ := by
  let S := frontier A
  let d := Metric.infDist p S
  have A_nonempty: A.Nonempty := by use p; exact interior_subset hp
  have d_pos: 0 < d := by
    unfold d S
    rw[←Metric.infDist_pos_iff_notMem_closure (nonempty_frontier_of_compact_nonempty_subset hn h_A_compact A_nonempty), isClosed_frontier.closure_eq]
    unfold frontier
    refine Set.notMem_of_mem_compl ?_
    rw [Set.compl_diff]
    left
    exact hp
  use d, d_pos
  intro x x_in_A x_ne_p
  let t₀ := sSup (seg_inside p x A)
  have limit_in_A: p + t₀ • (x - p) ∈ A := by
    have A_closed: IsClosed A := by exact IsCompact.isClosed h_A_compact
    rcases (seg_inside_has_lub p x A h_A_compact x_ne_p x_in_A).exists_seq_monotone_tendsto (seg_inside_nonempty p x A x_in_A) with ⟨u, h_u_monotone, h_u_bound, h_u_tendsto, h_u_mem⟩
    let f := f_ray p x
    show f t₀ ∈ A
    have f_t₀_limit: Filter.Tendsto (f ∘ u) Filter.atTop (𝓝 (f t₀)) := by
      apply Filter.Tendsto.comp
      . apply (f_ray_cont p x).continuousAt
      . exact h_u_tendsto
    apply A_closed.mem_of_tendsto f_t₀_limit
    exact Filter.Eventually.of_forall h_u_mem
  have limit_not_in_interior_A: p + t₀ • (x - p) ∉ interior A := by
    by_contra! h_mem_interior
    let U := (f_ray p x) ⁻¹' (interior A)
    have t₀_in_U: t₀ ∈ U := h_mem_interior
    have U_open: IsOpen U := (f_ray_cont p x).isOpen_preimage _ (isOpen_interior (s:= A))
    have: ∃ t' ∈ U, t' > t₀ := by
      rcases Metric.eventually_nhds_iff.mp (IsOpen.eventually_mem U_open t₀_in_U) with ⟨δ, δ_pos, hδ⟩
      use t₀ + δ / 2
      constructor
      . apply hδ
        simpa [abs_of_pos δ_pos]
      . linarith
    rcases this with ⟨t', t'_in_U, t'_gt_t₀⟩
    rcases (seg_inside_has_lub p x A h_A_compact x_ne_p x_in_A) with ⟨t₀_is_upper_bound, _⟩
    have: t' ≤ t₀ := by
      apply t₀_is_upper_bound
      simp [seg_inside]
      apply interior_subset
      exact t'_in_U
    linarith
  have limit_mem_frontier_A: p + t₀ • (x - p) ∈ frontier A := by
    unfold frontier
    rw [Set.mem_diff]
    refine ⟨?_, limit_not_in_interior_A⟩
    rwa [h_A_compact.isClosed.closure_eq]
  calc
    d ≤ dist p (p + t₀ • (x - p)) := Metric.infDist_le_dist_of_mem limit_mem_frontier_A (x := p)
    _ = sSup (seg_inside p x A) * ‖x - p‖ := by
      simp [norm_smul]
      left
      rw [abs_of_pos (seg_inside_sup_pos p x A h_A_compact x_ne_p x_in_A)]

lemma inv_cont_at_non_zero {x: ℝ} (hx: x ≠ 0): ContinuousAt (fun r:ℝ ↦ 1 / r) x := by
  rw [Metric.continuousAt_iff]
  intro ε εpos
  let δ := min (|x| * |x| * ε / 2) (|x| / 2)
  have abs_x_pos : |x| > 0 := abs_pos.mpr hx
  have δpos: δ > 0 := by
    apply lt_min
    . refine half_pos ?_
      exact mul_pos (mul_self_pos.mpr (ne_of_gt abs_x_pos)) εpos
    . exact half_pos abs_x_pos
  use δ, δpos
  intro y hy
  show |1/y - 1/x| < ε
  have abs_y_gt_half_abs_x: |y| > |x| / 2 := by
    calc
      |y| = |x - (x - y)| := by simp
      _ ≥ |(|x| - |x - y|)| := by apply abs_abs_sub_abs_le
      _ ≥ |x| - |x - y| := le_abs_self (|x| - |x - y|)
      _ > |x| - δ := by apply sub_lt_sub_left; rwa [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] at hy
      _ ≥ |x| - (|x| / 2) := by apply tsub_le_tsub_left; apply min_le_right
      _ = |x| / 2 := sub_half |x|
  have y_ne_0 : y ≠ 0 := by -- this is required for invoking field_simp
    suffices |y| > 0 by
      exact abs_pos.mp this
    calc
      |y| > |x| / 2 := abs_y_gt_half_abs_x
      _ > 0 := half_pos abs_x_pos
  field_simp
  rw [abs_div, div_lt_iff₀ (abs_pos.mpr ((mul_ne_zero_iff_right hx).mpr y_ne_0))]
  calc
    |x - y| < δ := by rw [abs_sub_comm]; exact hy
    _ ≤ (|x| * |x| * ε / 2) := by apply min_le_left
    _ = ε * (|x| * |x| / 2) := by field_simp; ring
    _ < ε * |y * x| := by rw [mul_lt_mul_left εpos, abs_mul, mul_comm |y| |x|, mul_div_assoc, mul_lt_mul_left abs_x_pos]; exact abs_y_gt_half_abs_x

theorem sep_fun_cont {p: EuclideanSpace ℝ (Fin n)} {A: Set (EuclideanSpace ℝ (Fin n))} (hn: n > 0) (h_A_convex: Convex ℝ A) (h_A_compact: IsCompact A) (hp: p ∈ interior A): Continuous (sep_fun p A) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x p with x_eq_p | x_ne_p
  . rw [x_eq_p, Metric.continuousAt_iff]
    intro ε ε_pos
    rcases interior_boundary_min_dist hn h_A_compact hp with ⟨d, d_pos, hd⟩
    rcases Metric.eventually_nhds_iff.mp (IsOpen.eventually_mem (isOpen_interior (s := A)) hp) with ⟨δ', δ'_pos, hδ'⟩
    use (min δ' (d * ε))
    constructor
    . exact lt_min δ'_pos (Left.mul_pos d_pos ε_pos)
    . intro x' hx'
      rcases eq_or_ne x' p with x'_eq_p | x'_ne_p
      . simpa [x'_eq_p]
      . simp [sep_fun, x'_ne_p]
        have x'_in_A : x' ∈ A := by
          apply interior_subset
          apply hδ'
          exact lt_of_lt_of_le (b := min δ' (d * ε)) hx' (min_le_left δ' (d * ε))
        let t := sSup (seg_inside p x' A)
        have t_pos : t > 0 := seg_inside_sup_pos p x' A h_A_compact x'_ne_p x'_in_A
        rw [abs_of_pos t_pos]
        have h_le: t⁻¹ ≤ d⁻¹ * ‖x' - p‖ := (le_inv_mul_iff₀' d_pos).mpr ((mul_inv_le_iff₀' t_pos).mpr (hd _ x'_in_A x'_ne_p))
        apply lt_of_le_of_lt (b:= d⁻¹ * ‖x' - p‖) h_le
        have norm_lt: ‖x' - p‖ < d * ε := lt_of_lt_of_le hx' (min_le_right δ' (d * ε))
        apply lt_of_lt_of_eq (b := d ⁻¹ * (d * ε))
        . exact (mul_lt_mul_iff_of_pos_left (Right.inv_pos.mpr d_pos)).mpr norm_lt
        . exact inv_mul_cancel_left₀ (ne_of_lt d_pos).symm ε
  . have h_eventually_eq: sep_fun p A =ᶠ[𝓝 x] ((fun r:ℝ ↦ 1 / r) ∘ (fun x ↦ sSup (seg_inside p x A))) := by
      -- this lemma is to show that on a neighbor of x the sep function can be rewritten to composition of two other functions
      rcases t2_separation x_ne_p with ⟨U, ⟨V, U_open, V_open, x_in_U, p_in_V, U_V_disjoint⟩⟩
      apply Filter.sets_of_superset (x := U)
      . show U ∈ (𝓝 x)
        rw [mem_nhds_iff]
        use U
      . intro x' x'_in_U
        have x'_ne_p: x' ≠ p := by
          by_contra! heq
          rw [heq] at x'_in_U
          have : p ∈ U ∩ V := Set.mem_inter x'_in_U p_in_V
          rw [Set.disjoint_iff_inter_eq_empty] at U_V_disjoint
          rw [U_V_disjoint] at this
          contradiction
        simp [sep_fun, x'_ne_p]
    suffices ContinuousAt ((fun r:ℝ ↦ 1 / r) ∘ (fun x ↦ sSup (seg_inside p x A))) x by
      exact ContinuousAt.congr this (id (Filter.EventuallyEq.symm h_eventually_eq))
    refine ContinuousAt.comp ?_ ?_
    . exact inv_cont_at_non_zero (ne_of_gt (seg_inside_sup_pos_of_interior p x A h_A_compact x_ne_p hp))
    . sorry
end
end Chp5

-- Coeherent Defs
namespace Chp5
/-the topological space parameter turns out need not be explicit here-/
structure IsCoeherent {X: Type*} [TopologicalSpace X] (B: Set (Set X)) : Prop where
    open_crit: ∀ s : Set X, IsOpen s ↔ ∀ b ∈ B, IsOpen (((↑): b → X)⁻¹' s)
    cover: ⋃₀ B = Set.univ

def CoeherentSigmaMap {X: Type*} [TopologicalSpace X] (B: Set (Set X)) := fun (x: Sigma (fun b:B ↦ b.1)) ↦ x.2.1

theorem subset_open_of_open {X: Type*} [TopologicalSpace X] {s V: Set X} (hV: IsOpen V) : IsOpen (((↑): s → X) ⁻¹' V) := by
    exact isOpen_induced hV

theorem coeherent_of_closed_crit_and_cover {X: Type*} [TopologicalSpace X] {B: Set (Set X)}
    (h_close_crit: ∀ s : Set X, IsClosed s ↔ ∀ b ∈ B, IsClosed (((↑): b → X)⁻¹' s))
    (h_cover: ⋃₀ B = Set.univ) : IsCoeherent B where
        cover := h_cover
        open_crit := by
            intro s
            constructor
            . intro hs b hb
              apply isOpen_induced hs
            intro h
            rw [←isClosed_compl_iff, h_close_crit]
            simpa using h

theorem coeherent_of_closed_crit_and_cover' {X: Type*} [TopologicalSpace X] {B: Set (Set X)} (h_close_crit': ∀ s : Set X, (∀ b ∈ B, IsClosed (((↑): b → X)⁻¹' s)) → IsClosed s) (h_cover: ⋃₀ B = Set.univ) : IsCoeherent B := by
    refine coeherent_of_closed_crit_and_cover ?_ h_cover
    intro s
    constructor
    case mp =>
        intro hs b hb
        refine IsClosed.preimage ?_ hs
        exact continuous_subtype_val
    case mpr => exact h_close_crit' s

theorem closed_crit_of_coeherent {X: Type*} [TopologicalSpace X] {B: Set (Set X)} (h_coeherent: IsCoeherent B) : ∀ s: Set X, (∀ b ∈ B, IsClosed (((↑): b → X)⁻¹' s)) → IsClosed s := by
    intro s hs
    rw [←isOpen_compl_iff]
    have : ∀ b ∈ B,  IsOpen (((↑):b → X) ⁻¹' sᶜ) := by
        intro b hb
        simpa using hs b hb
    exact (h_coeherent.open_crit sᶜ).mpr this

/-Proposition 5.2.a-/
theorem continuous_of_coherent {X: Type*} [TopologicalSpace X] {B: Set (Set X)} (hx: IsCoeherent B) {Y: Type*} [TopologicalSpace Y] (f: X → Y): Continuous f ↔ ∀b ∈ B, Continuous (b.restrict f) := by
    constructor
    . intro fc b hb
      exact Pi.continuous_restrict_apply b fc
    intro hf
    rw [continuous_def]
    intro s hs
    rw [hx.open_crit  (f ⁻¹' s)]
    intro b hb
    specialize hf b hb
    rw [continuous_def] at hf
    specialize hf s hs
    simpa using hf

/-
Proposition 5.2.b
Disjoint union is represented with Sigma type, note the sigma topological space is implicitly used
-/
theorem quotient_of_choherent {X: Type*} [TX:TopologicalSpace X] {B: Set (Set X)} (hB: IsCoeherent B):
    Topology.IsQuotientMap (CoeherentSigmaMap B) where
        surjective := by
            intro x
            have : ∃ b ∈ B, x ∈ b := by
                apply Set.mem_sUnion.mp
                rw [hB.cover]
                trivial
            rcases this with ⟨b, hb, hxb⟩
            use ⟨⟨b, hb⟩, ⟨x, hxb⟩⟩
            rw [CoeherentSigmaMap]
        eq_coinduced := by
            rw [TopologicalSpace.ext_iff]
            intro s
            have :  @IsOpen X (TopologicalSpace.coinduced (CoeherentSigmaMap B) instTopologicalSpaceSigma) s ↔ IsOpen ((CoeherentSigmaMap B)⁻¹' s) := by rfl
            rw [this, isOpen_sigma_iff]
            have : CoeherentSigmaMap B ⁻¹' s = {p | p.2.val ∈ s} := by rfl
            simp only [this]
            have : ∀ i:B, ((Sigma.mk i):_ → Sigma (fun b:B ↦ b.1)) ⁻¹' {p | ↑p.snd ∈ s} = {x | x.1 ∈ s} := by intro i; simp
            simp only [this]
            simpa using hB.open_crit s

section
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
theorem embedding_of_closed_continuous_injective {f : X → Y} (f_closed_map: IsClosedMap f) (f_continuous: Continuous f) (f_injective : Function.Injective f): Topology.IsEmbedding f := by
    refine (Topology.isEmbedding_iff f).mpr ⟨?_, f_injective⟩
    rw [Topology.isInducing_iff]
    ext s
    refine Iff.intro ?mp ?mpr
    case mp =>
        intro s_open_in_X
        refine isOpen_mk.mpr ?_
        use (f '' s) ∪ (Set.range f)ᶜ
        have : IsOpen (f '' s ∪ (Set.range f)ᶜ) := by
            rw [←isClosed_compl_iff]
            simp
            have : (f '' s)ᶜ ∩ (Set.range f) = f '' sᶜ := by
                ext y
                simp
                refine Iff.intro ?mp1 ?mpr1
                case mp1 =>
                    rintro ⟨h1, x, rfl⟩
                    use x
                    simp
                    contrapose! h1
                    use x
                case mpr1 =>
                    rintro ⟨x, x_not_in_s, rfl⟩
                    refine ⟨?_, (by use x)⟩
                    intro x₀ x₀_in_s
                    contrapose! x_not_in_s
                    have : x₀ = x := by apply f_injective x_not_in_s
                    rwa [←this]
            rw [this]
            apply f_closed_map
            rwa [isClosed_compl_iff]
        use this
        simp
        exact Function.Injective.preimage_image f_injective s
    case mpr =>
        intro hs
        rw [isOpen_mk] at hs
        rcases hs with ⟨t, t_open_in_Y, rfl⟩
        exact f_continuous.isOpen_preimage t t_open_in_Y

theorem embedding_of_open_continuous_injective {f: X → Y} (f_open_map: IsOpenMap f) (f_continuous: Continuous f) (f_injective: Function.Injective f): Topology.IsEmbedding f := by
  refine (Topology.isEmbedding_iff f).mpr ⟨?_, f_injective⟩
  rw [Topology.isInducing_iff]
  ext s
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro s_open_in_X
    refine isOpen_mk.mpr ?_
    use f '' s
    have : IsOpen (f '' s) := f_open_map s s_open_in_X
    use this
    exact Function.Injective.preimage_image f_injective s
  case mpr =>
    intro hs
    rw [isOpen_mk] at hs
    rcases hs with ⟨t, t_open_in_Y, rfl⟩
    exact f_continuous.isOpen_preimage t t_open_in_Y
end

section
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (A: Set Y) (f : A → X)
def glue_rel : (X ⊕ Y) → (X ⊕ Y) → Prop := fun u v => ∃ a : A, u = Sum.inl (f a) ∧ v = Sum.inr a.1

def glue_rel_equiv : (X ⊕ Y) → (X ⊕ Y) → Prop := Relation.EqvGen (glue_rel A f)

def glue_setoid : Setoid (X ⊕ Y) where
    r := glue_rel_equiv A f
    iseqv := Relation.EqvGen.is_equivalence _

abbrev AdjointSpace : Type _ := Quotient (glue_setoid A f)

instance: TopologicalSpace (AdjointSpace A f) := by
    infer_instance

def adj_proj: (X ⊕ Y) → AdjointSpace A f := Quotient.mk _

theorem adj_proj_quotient: Topology.IsQuotientMap (adj_proj A f) := by
    rw [adj_proj]
    exact { surjective := Quotient.mk_surjective, eq_coinduced := rfl }

def left_adj_proj : X → AdjointSpace A f := (adj_proj A f)∘ (Sum.inl)

-- The recursor is really a function version of mathematical induction
-- the key insight, quote from "theorem proving in Lean", is that "The intuition is that an inductive type is exhaustively generated by the constructors, and has no elements beyond those they construct."
-- the recursor takes a "motive" that takes arguments of target type and maps to some other Type(s)
-- in case of EqvGen, the motive is of type: (a a_1 : α) → Relation.EqvGen r a a_1 → Prop
-- so we can use the recursor to prove other propositions
-- the function only requires proving the motive holds for direct invocation of constructor
-- which is analogous to the induction step of mathematical induction
#check Relation.EqvGen.rec

omit [TopologicalSpace X] [TopologicalSpace Y] in theorem glue_rel_equiv_explicit : ∀ xy1 xy2: (X ⊕ Y), ((glue_rel_equiv A f) xy1 xy2) →
(∃ x:X, xy1 = Sum.inl x ∧ xy2 = xy1) ∨
(∃ x1:X, ∃ y2:Y, ∃ y2':A, xy1 = Sum.inl x1 ∧ xy2 = Sum.inr y2 ∧ y2 = y2'.1 ∧ x1 = f y2') ∨
(∃ y1:Y, ∃ x2:X, ∃ y1':A, xy1= Sum.inr y1 ∧ xy2 = Sum.inl x2 ∧ y1 = y1'.1 ∧ x2 = f y1') ∨
(∃ y1:Y, ∃ y2:Y, ∃ y1' y2':A, xy1 = Sum.inr y1 ∧ xy2 = Sum.inr y2 ∧ y1'.1 = y1 ∧ y2'.1 = y2 ∧ f y1' = f y2' ∧ y1 ≠ y2) ∨
(∃ y:Y, xy1 = Sum.inr y ∧ xy2 = xy1) := by
    apply @Relation.EqvGen.rec
    case rel =>
        intro xy1 xy2 hxy12
        rw [glue_rel] at hxy12
        right; left
        rcases hxy12 with ⟨y', heq1, heq2⟩
        use (f y'), y'.1, y'
    case refl =>
        intro xy
        match xy with
        | Sum.inl x => left; use x
        | Sum.inr y => right; right; right; right; use y
    case symm =>
        intro xy1 xy2 h_rel hxy12
        rcases hxy12 with c12_0 | c12_1 | c12_2 | c12_3 | c12_4
        . rcases c12_0 with ⟨x21, hx21, heq21⟩
          left
          use x21, (by rwa[heq21]), heq21.symm
        . rcases c12_1 with ⟨x1, y2, y2', heq12_0, heq12_1, heq12_2, heq12_3⟩
          right; right; left
          use y2, x1, y2'
        . rcases c12_2 with ⟨y12, x12, y12', heq12_1, heq12_2, heq12_3, heq12_4⟩
          right; left
          use x12, y12, y12'
        . rcases c12_3 with ⟨y12_0, y12_1, y12_0', y12_1', heq12_1, heq12_2, heq12_3, heq12_4, heq12_5, hne12⟩
          right; right; right; left
          use y12_1, y12_0, y12_1', y12_0', heq12_2, heq12_1, heq12_4, heq12_3, heq12_5.symm, hne12.symm
        . rcases c12_4 with ⟨y12, heq12_1, heq12_2⟩
          right; right; right; right;
          use y12, (by rwa[heq12_2]), heq12_2.symm
    case trans =>
        intro xy1 xy2 xy3 rxy12 rxy23 cases12 cases23
        rcases cases12 with c12_0 | c12_1 | c12_2 | c12_3 | c12_4
        . rcases c12_0 with ⟨x21, hx21, heq21⟩
          rcases cases23 with c23_0 | c23_1 | c23_2 | c23_3 | c23_4
          . rcases c23_0 with ⟨x23, hx23, heq23⟩
            have :  (∃ x, xy1 = Sum.inl x ∧ xy3 = xy1) := by
                use x21, hx21
                simp [←heq21, heq23]
            left
            assumption
          . rcases c23_1 with ⟨x23, y23, y23', heq1, heq2, heq3, heq4⟩
            right; left
            use x21, y23, y23', hx21, heq2, heq3
            have : x21 = x23 := by
                apply Sum.inl_injective
                rw [←hx21, ←heq1]
                exact heq21.symm
            rw [this]
            exact heq4
          . rcases c23_2 with ⟨y23, x23, y23', heq⟩
            have : Sum.inl x21 = Sum.inr y23 := by
                rw [←hx21, ←heq.1]
                exact heq21.symm
            contradiction
          . rcases c23_3 with ⟨y2, y3, y2', y3', heq⟩
            have : Sum.inl x21 = Sum.inr y2 := by
                rw [←hx21, ←heq.1]
                exact heq21.symm
            contradiction
          . rcases c23_4 with ⟨y2, heq⟩
            have : Sum.inl x21 = Sum.inr y2 := by
                rw [←hx21, ←heq.1]
                exact heq21.symm
            contradiction
        . rcases c12_1 with ⟨x1, y2, y2', heq12_0, heq12_1, heq12_2, heq12_3⟩
          rcases cases23 with c23_0 | c23_1 | c23_2 | c23_3 | c23_4
          . rcases c23_0 with ⟨x2, heq23⟩
            have : Sum.inl x2 = Sum.inr y2 := by rw [←heq23.1, heq12_1]
            contradiction
          . rcases c23_1 with ⟨x23, y23, y23', heq1, heq2, heq3, heq4⟩
            have : Sum.inr y2 = Sum.inl x23 := by rw [←heq12_1, heq1]
            contradiction
          . rcases c23_2 with ⟨y23, x23, y23', heq1, heq2, heq3, heq4⟩
            have y2_eq_y23 : y2 = y23 := by
                apply Sum.inr_injective
                rw [←heq12_1, ←heq1]
            have y2'_eq_y23' : y2' = y23' := by
                apply SetCoe.ext
                rw [←heq12_2, ←heq3]
                exact  y2_eq_y23
            have x1_eq_x23: x1 = x23 := by
                rw  [heq12_3, heq4]
                congr
            have xy1_eq_xy3 : xy1 = xy3 := by
                rw [heq12_0, heq2]
                congr
            left
            use x1, heq12_0, xy1_eq_xy3.symm
          . rcases c23_3 with ⟨y20, y30, y20', y30', heq1, heq2, heq3, heq4, heq5, hne⟩
            right; left
            use x1, y30, y30', heq12_0, heq2, heq4.symm
            have : y2 = y20 := by apply Sum.inr_injective; rw [←heq12_1, ←heq1]
            have : y2' = y20' := by apply SetCoe.ext; rwa [←heq12_2, heq3]
            rwa [heq12_3, this]
          . rcases c23_4 with ⟨y, heq⟩
            right; left
            use x1, y2, y2', heq12_0
            rw [heq.2]
            use heq12_1
        . rcases c12_2 with ⟨y12, x12, y12', heq12_1, heq12_2, heq12_3, heq12_4⟩
          rcases cases23 with c23_0 | c23_1 | c23_2 | c23_3 | c23_4
          . rcases c23_0 with ⟨x2, heq0, heq1⟩
            right; right; left
            use y12, x2, y12', heq12_1, (by rwa[heq1]), heq12_3
            have : x2 = x12 := by apply Sum.inl_injective; rw[←heq12_2, ←heq0]
            rwa [this]
          . rcases c23_1 with ⟨x23, y23, y23', heq1, heq2, heq3, heq4⟩
            -- in this case we need to check if y12 == y23
            rcases eq_or_ne y12 y23 with h_y12_eq_y23 | h_y12_ne_y23
            . right; right; right; right
              use y12, heq12_1
              rwa [heq12_1, h_y12_eq_y23]
            . right; right; right; left
              use y12, y23, y12', y23', heq12_1, heq2, heq12_3.symm, heq3.symm
              have : f y12' = f y23' := by
                rw [←heq12_4, ←heq4]
                apply Sum.inl_injective
                rwa [←heq12_2]
              use this
          . rcases c23_2 with ⟨y23, x23, y23', heq1, heq2, heq3, heq4⟩
            have : Sum.inl x12 = Sum.inr y23 := by rwa [←heq12_2]
            contradiction
          . rcases c23_3 with ⟨y20, y30, y20', y30', heq1, heq2, heq3, heq4, heq5, hne⟩
            have : Sum.inl x12 = Sum.inr y20 := by rwa [←heq12_2]
            contradiction
          . rcases c23_4 with ⟨y, heq1, heq2⟩
            have: Sum.inl x12 = Sum.inr y := by rwa[←heq12_2]
            contradiction
        . rcases c12_3 with ⟨y12_0, y12_1, y12_0', y12_1', heq12_1, heq12_2, heq12_3, heq12_4, heq12_5, hne12⟩
          rcases cases23 with c23_0 | c23_1 | c23_2 | c23_3 | c23_4
          . rcases c23_0 with ⟨x2, heq0, heq1⟩
            have : Sum.inr y12_1 = Sum.inl x2 := by rwa[←heq12_2]
            contradiction
          . rcases c23_1 with ⟨x23, y23, y23', heq1, heq2, heq3, heq4⟩
            have : Sum.inr y12_1 = Sum.inl x23 := by rwa[←heq12_2]
            contradiction
          . rcases c23_2 with ⟨y23, x23, y23', heq1, heq2, heq3, heq4⟩
            right; right; left
            use y12_0, x23, y12_0', heq12_1, heq2, heq12_3.symm
            rw [heq4, heq12_5]; congr
            apply SetCoe.ext
            rw [heq12_4, ←heq3]
            apply Sum.inr_injective
            rwa [←heq1]
          . rcases c23_3 with ⟨y20, y30, y20', y30', heq1, heq2, heq3, heq4, heq5, hne⟩
            rcases eq_or_ne y12_0 y30 with h_y12_0_eq_y30 | h_y12_0_ne_y30
            . right; right; right; right
              use y12_0, heq12_1
              rw [heq2, ←h_y12_0_eq_y30, heq12_1]
            . right; right; right; left
              use y12_0, y30, y12_0', y30', heq12_1, heq2, heq12_3, heq4
              have : f y12_0' = f y30' := by
                rw [heq12_5, ←heq5]
                congr
                apply SetCoe.ext
                rw [heq12_4, heq3]
                apply Sum.inr_injective
                rwa [←heq12_2]
              use this
          . rcases c23_4 with ⟨y, heq⟩
            right; right; right; left
            use y12_0, y12_1, y12_0', y12_1', heq12_1, (by rwa[heq.2])
        . rcases c12_4 with ⟨y12, heq12_1, heq12_2⟩
          rcases cases23 with c23_0 | c23_1 | c23_2 | c23_3 | c23_4
          . rcases c23_0 with ⟨x2, heq0, heq1⟩
            have : Sum.inl x2 = Sum.inr y12 := by rwa [←heq0, ←heq12_1]
            contradiction
          . rcases c23_1 with ⟨x23, y23, y23', heq1, heq2, heq3, heq4⟩
            have : Sum.inl x23 = Sum.inr y12 := by rwa [←heq1, heq12_2]
            contradiction
          . rcases c23_2 with ⟨y23, x23, y23', heq1, heq2, heq3, heq4⟩
            right; right; left
            use y12, x23, y23', heq12_1, heq2, (by rw [←heq3]; apply Sum.inr_injective; rwa [←heq12_1, ←heq12_2])
          . rcases c23_3 with ⟨y20, y30, y20', y30', heq1, heq2, heq3, heq4, heq5, hne⟩
            right; right; right; left
            use y20, y30, y20', y30', (by rwa [←heq12_2])
          . rcases c23_4 with ⟨y, heq⟩
            right; right; right; right
            use y12, heq12_1, (by rwa[heq.2])

-- as an example, we use recursor to prove the left_adj_proj is injective
omit [TopologicalSpace X] [TopologicalSpace Y] in theorem left_adj_proj_inj : Function.Injective (left_adj_proj A f) := by
    intro a b hab
    rw [left_adj_proj, adj_proj] at hab
    have : (glue_setoid A f).r (Sum.inl a) (Sum.inl b) := by
        exact Quotient.eq''.mp hab
    simp [glue_setoid] at this
    rcases glue_rel_equiv_explicit A f _ _ this with c_0 | c_1 | c_2 | c_3 | c_4
    . rcases c_0 with ⟨x, heq1, heq2⟩
      apply Sum.inl_injective
      exact heq2.symm
    . rcases c_1 with ⟨x, y, y', heq1, heq2, heq3, heq4⟩
      contradiction
    . rcases c_2 with ⟨y, x, y', heq1, heq2, heq3, heq4⟩
      contradiction
    . rcases c_3 with ⟨y1, y2, y1', y2', heq1, heq2, heq3, heq4, hne⟩
      contradiction
    . rcases c_4 with ⟨y, heq1, heq2⟩
      contradiction

theorem left_adj_proj_closed_map (hA: IsClosed A) (hf: Continuous f): IsClosedMap (left_adj_proj A f) := by
    intro B BClosed
    rw [left_adj_proj, Set.image_comp, ←(adj_proj_quotient A f).isClosed_preimage, isClosed_sum_iff]
    refine And.intro ?left ?right
    case left =>
        have : (Sum.inl ⁻¹' (adj_proj A f ⁻¹' (adj_proj A f '' (Sum.inl '' B)))) = B := by
            ext x
            refine Iff.intro ?mem_left ?mem_right
            case mem_left =>
                intro hx
                simp at hx
                rcases hx with ⟨a, a_in_B, ha⟩
                have : a = x := by
                    apply left_adj_proj_inj A f
                    exact ha
                rwa [←this]
            case mem_right =>
                intro hx
                simp
                use x
        rwa [this]
    case right =>
        let g : A → Y := (↑)
        have : Sum.inr ⁻¹' (adj_proj A f ⁻¹' (adj_proj A f '' (Sum.inl '' B))) = g '' (f ⁻¹' B) := by
            ext y
            refine Iff.intro ?mem_left ?mem_right
            case mem_left =>
                intro hy
                simp
                simp[adj_proj] at hy
                rcases hy with ⟨x, x_in_B, hxy⟩
                rcases glue_rel_equiv_explicit A f (Sum.inl x) (Sum.inr y) hxy with c0 | c1 | c2 | c3 | c4
                . rcases c0 with ⟨x₀, hx₀, hxy'⟩
                  contradiction
                . rcases c1 with ⟨x₀, y₀, y₀', heq1, heq2, heq3, heq4⟩
                  have x_eq_x₀ : x = x₀ := by apply Sum.inl_injective; assumption
                  have y_eq_y₀ : y = y₀ := by apply Sum.inr_injective; assumption
                  use y₀'.1, y₀'.2, (by rwa [←heq4, ←x_eq_x₀])
                  simp [g]
                  rw [←heq3, y_eq_y₀]
                . rcases c2 with ⟨y₀, x₀, y₀', heq1, heq2, heq3, heq4⟩
                  contradiction
                . rcases c3 with ⟨y₀, y₁, y₀', y₁', heq1, heq2⟩
                  contradiction
                . rcases c4 with ⟨y₀, heq1, heq2⟩
                  contradiction
            case mem_right =>
                intro hy
                rcases hy with ⟨y', fy'_in_B, rfl⟩
                simp
                use (f y'), fy'_in_B
                simp [adj_proj, glue_setoid]
                apply Relation.EqvGen.rel
                use y'
        rw [this]
        exact IsClosed.trans (IsClosed.preimage hf BClosed) hA



theorem left_adj_proj_is_embedding (hA: IsClosed A) (hf: Continuous f) : Topology.IsEmbedding (left_adj_proj A f):= by
    refine embedding_of_closed_continuous_injective (left_adj_proj_closed_map A f hA hf) ?_ (left_adj_proj_inj A f)
    rw [left_adj_proj, adj_proj]
    refine Continuous.comp ?_ ?_
    exact { isOpen_preimage := fun s a ↦ a }
    exact continuous_inl

def right_adj_proj : (Aᶜ:Set Y) → AdjointSpace A f := (adj_proj A f) ∘ (Sum.inr) ∘ (Subtype.val)

omit [TopologicalSpace X] [TopologicalSpace Y] in theorem right_adj_proj_injective : Function.Injective (right_adj_proj A f) := by
    intro a b hab
    rw [right_adj_proj, adj_proj] at hab
    have : (glue_setoid A f).r (Sum.inr a.1) (Sum.inr b.1) := Quotient.eq''.mp hab
    simp [glue_setoid] at this
    rcases glue_rel_equiv_explicit A f _ _ this with c0 | c1 | c2 | c3 | c4
    . rcases c0 with ⟨x, heq1, heq2⟩
      contradiction
    . rcases c1 with ⟨x, y, y', heq1, heq2, heq3, heq4⟩
      contradiction
    . rcases c2 with ⟨y, x, y', heq1, heq2, heq3, heq4⟩
      contradiction
    . rcases c3 with ⟨y1, y2, y1', y2', heq1, heq2, heq3, heq4, heq5, hne⟩
      have a_in_A: a.1 ∈ A := by
        have : a.1 = y1 := by
            apply Sum.inr_injective
            exact heq1
        rw [this, ←heq3]
        exact y1'.2
      have a_not_in_A : a.1 ∉ A := a.2
      contradiction
    . rcases c4 with ⟨y, heq1, heq2⟩
      have : b.1 = a.1 := by
        apply Sum.inr_injective
        exact heq2
      apply SetCoe.ext
      exact this.symm

theorem right_adj_proj_open_map (hA: IsClosed A): IsOpenMap (right_adj_proj A f) := by
  let g : (Aᶜ: Set Y) → Y := (↑)
  intro U U_open_in_A_compl
  rw [right_adj_proj, Set.image_comp, Set.image_comp]
  let V := g '' U
  let W: (Set (X ⊕ Y)) := Sum.inr '' V
  have : IsOpen V := IsOpen.trans U_open_in_A_compl IsClosed.isOpen_compl
  have W_open: IsOpen W := (Topology.IsOpenEmbedding.isOpen_iff_image_isOpen Topology.IsOpenEmbedding.inr).mp this
  have V_sub_A_compl : V ⊆ Aᶜ := by exact Subtype.coe_image_subset Aᶜ U
  show IsOpen ((adj_proj A f) '' W)
  rw [←(adj_proj_quotient A f).isOpen_preimage]
  suffices adj_proj A f ⁻¹' (adj_proj A f '' W) = W by rwa [this]
  ext xy
  refine Iff.intro ?mp ?mpr
  case mpr =>
    intro xy_in_W
    use xy
  case mp =>
    rintro ⟨xy', xy'_in_W, heq⟩
    let ⟨y₀, y₀_in_V, heq'⟩ := xy'_in_W
    have : (glue_setoid A f) xy' xy := by
      exact Quotient.eq''.mp heq
    simp [glue_setoid] at this
    rcases glue_rel_equiv_explicit A f xy' xy this with c0 | c1 | c2 | c3 | c4
    . rcases c0 with ⟨x, heq1, heq2⟩
      rw [←heq'] at heq1
      contradiction
    . rcases c1 with ⟨x, y₁, y₁', heq1, heq2⟩
      rw [←heq'] at heq1
      contradiction
    . rcases c2 with ⟨y₁, x₂, y₁', heq1, heq2, heq3, heq4⟩
      have: y₀ = y₁ := by
        rw [←heq'] at heq1
        apply Sum.inr_injective
        exact heq1
      have y₀_in_A : y₀ ∈ A := by
        rw [this, heq3]
        exact y₁'.2
      have y₀_in_A_compl : y₀ ∈ Aᶜ := V_sub_A_compl y₀_in_V
      contradiction
    . rcases c3 with ⟨y₁, y₂, y₁', y₂', heq1, heq2, heq3, heq4, heq5, hne⟩
      have: y₀ = y₁ := by
        rw [←heq'] at heq1
        apply Sum.inr_injective
        exact heq1
      have y₀_in_A : y₀ ∈ A := by
        rw [this, ←heq3]
        exact y₁'.2
      have y₀_in_A_compl : y₀ ∈ Aᶜ := V_sub_A_compl y₀_in_V
      contradiction
    . rcases c4 with ⟨y, heq1, heq2⟩
      rwa [heq2]

theorem right_adj_proj_is_embedding (hA: IsClosed A) : Topology.IsEmbedding (right_adj_proj A f) := by
    refine embedding_of_open_continuous_injective (right_adj_proj_open_map A f hA) ?_ (right_adj_proj_injective A f)
    rw [right_adj_proj]
    refine Continuous.comp ?_ ?_
    exact { isOpen_preimage := fun s a ↦ a }
    continuity

omit [TopologicalSpace X] [TopologicalSpace Y] in theorem glue_setoid_of_same_image {y₁ y₂: Y} (y₁_in_A: y₁ ∈ A) (y₂_in_A: y₂ ∈ A) (heq: f ⟨y₁, y₁_in_A⟩ = f ⟨y₂, y₂_in_A⟩): (glue_setoid A f) (Sum.inr y₁) (Sum.inr y₂) := by
  simp [glue_setoid]
  let x := f ⟨y₁, y₁_in_A⟩
  have relxy₁: (glue_rel_equiv A f) (Sum.inl x) (Sum.inr y₁) := by
    apply Relation.EqvGen.rel
    use ⟨y₁, y₁_in_A⟩
  have relxy₂: (glue_rel_equiv A f) (Sum.inl x) (Sum.inr y₂) := by
    apply Relation.EqvGen.rel
    use ⟨y₂, y₂_in_A⟩
    simp [←heq, x]
  exact Relation.EqvGen.trans (Sum.inr y₁) (Sum.inl x) (Sum.inr y₂) (relxy₁.symm) relxy₂
omit [TopologicalSpace X] [TopologicalSpace Y] in theorem left_adj_right_adj_range_disjoint: Disjoint (Set.range (left_adj_proj A f)) (Set.range (right_adj_proj A f)) := by
  by_contra goal
  rw [Set.not_disjoint_iff_nonempty_inter] at goal
  rcases goal with ⟨w, ⟨x, h_xw⟩, ⟨y, h_yw⟩⟩
  have hxy: left_adj_proj A f x = right_adj_proj A f y := by rw [h_xw, h_yw]
  simp [left_adj_proj, right_adj_proj, adj_proj, glue_setoid] at hxy
  rcases glue_rel_equiv_explicit A f (Sum.inl x) (Sum.inr y.1) hxy with c1 | c2 | c3 | c4 | c5
  . rcases c1 with ⟨x', h1, h2⟩
    contradiction
  . rcases c2 with ⟨x', y₀, y', heq1, heq2, y₀_is_y', heq4⟩
    have y₀_is_y: y.1 = y₀ := by apply Sum.inr_injective; exact heq2
    have y₀_in_A: y₀ ∈ A := by rw [y₀_is_y']; exact y'.2
    have y₀_in_A_compl: y₀ ∈ Aᶜ := by rw [←y₀_is_y]; exact y.2
    contradiction
  . rcases c3 with ⟨_, _, _, heq1, _⟩
    contradiction
  . rcases c4 with ⟨_, _, _, _, heq1, _⟩
    contradiction
  . rcases c5 with ⟨_, heq1, _⟩
    contradiction

omit [TopologicalSpace X] [TopologicalSpace Y] in theorem left_adj_right_adj_cover: (Set.range (left_adj_proj A f)) ∪ (Set.range (right_adj_proj A f)) = Set.univ := by
  ext t
  simp
  rcases Quotient.exists_rep t with ⟨w, rfl⟩
  match w with
  | Sum.inl x =>
    left
    use x
    simp [left_adj_proj, adj_proj]
  | Sum.inr y =>
    rcases Classical.em (y ∈ A) with y_in_A | y_not_in_A
    . left
      use f ⟨y, y_in_A ⟩
      simp [left_adj_proj, adj_proj, glue_setoid]
      apply Relation.EqvGen.rel
      use ⟨y, y_in_A⟩
    . right
      use y, y_not_in_A
      simp [right_adj_proj, adj_proj]

lemma eq_compl_iff {Z: Type*} {s1 s2: Set Z} (h1: Disjoint s1 s2) (h2: s1 ∪ s2 = Set.univ) : s1 = s2ᶜ := by
  rw [Set.disjoint_iff_inter_eq_empty] at h1
  ext x
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro x_in_s1
    contrapose! h1
    simp at h1
    use x
    exact ⟨x_in_s1, h1⟩
  case mpr =>
    intro x_not_in_s2
    have: x ∈ s1 ∪ s2 := by rw [h2]; trivial
    rcases this with x_in_s1 | x_in_s2
    . exact x_in_s1
    contradiction

omit [TopologicalSpace X] [TopologicalSpace Y] in theorem left_range_eq_right_range_compl: Set.range (left_adj_proj A f) = (Set.range (right_adj_proj A f))ᶜ := by
  apply eq_compl_iff
  apply left_adj_right_adj_range_disjoint
  exact left_adj_right_adj_cover A f

omit [TopologicalSpace X] [TopologicalSpace Y] in theorem right_range_eq_left_range_compl: Set.range (right_adj_proj A f) = (Set.range (left_adj_proj A f))ᶜ := by
  simp [left_range_eq_right_range_compl]
omit [TopologicalSpace X] [TopologicalSpace Y] in theorem left_range_cover_glue_image: ((adj_proj A f) ∘ Sum.inr) '' A ⊆ Set.range (left_adj_proj A f) := by
  rintro z ⟨y, y_in_A, rfl⟩
  use f ⟨y, y_in_A⟩
  simp [left_adj_proj, adj_proj, glue_setoid]
  apply Relation.EqvGen.rel
  use ⟨y, y_in_A⟩
end

section
theorem quotient_lift_is_homeomorph {X Z: Type*} [TopologicalSpace X] [TopologicalSpace Z] {S: Setoid X} {g: X → Z}
  (h_g_factors: ∀ x₁ x₂: X, S x₁ x₂ → g x₁ = g x₂)
  (h_quotient_factors_on_g : ∀ x₁ x₂: X, g x₁ = g x₂ → S x₁ x₂)
  (g_quotient: Topology.IsQuotientMap g):
  IsHomeomorph (Quotient.lift g h_g_factors) := by
    let φ := Quotient.lift g h_g_factors
    show IsHomeomorph φ
    refine { continuous := ?is_continuous, isOpenMap := ?is_open_map, bijective := ?is_bijective }
    case is_continuous =>
      exact Continuous.quotient_lift (Topology.IsQuotientMap.continuous g_quotient) h_g_factors
    case is_open_map =>
      intro s s_open
      let t := (Quotient.mk S) ⁻¹' s
      have t_open : IsOpen t := s_open
      have φ_s_eq_g_t : φ '' s = g '' t := by
        ext z
        refine Iff.intro ?mp ?mpr
        case mp =>
          intro hz
          rcases hz with ⟨x', x'_in_s, heq⟩
          rcases Quotient.exists_rep x' with ⟨x, hx⟩
          rw [←heq, ←hx]
          show g x ∈ g '' t
          refine ⟨x, ?_, rfl⟩
          show Quotient.mk S x ∈ s
          rwa [hx]
        case mpr =>
          intro hz
          rcases hz with ⟨x, x_in_t, rfl⟩
          refine ⟨Quotient.mk S x, x_in_t, rfl ⟩
      have t_eq_preimage : g ⁻¹' (g '' t) = t := by
        ext x
        refine Iff.intro ?mp ?mpr
        case mp =>
          intro hgx
          rcases hgx with ⟨x', x'_in_t, heq⟩
          show Quotient.mk S x ∈ s
          rw [←Quotient.sound (h_quotient_factors_on_g _ _ heq)]
          exact x'_in_t
        case mpr =>
          intro hx
          use x
      rw [φ_s_eq_g_t]
      suffices IsOpen (g ⁻¹' (g '' t)) by
        exact (Topology.IsQuotientMap.isOpen_preimage g_quotient).mp this
      rw [t_eq_preimage]
      exact t_open
    case is_bijective =>
      refine ⟨?inj, ?bij⟩
      case inj =>
        intro x₁' x₂' heq'
        rcases Quotient.exists_rep x₁' with ⟨x₁, rfl⟩
        rcases Quotient.exists_rep x₂' with ⟨x₂, rfl⟩
        exact Quotient.sound (h_quotient_factors_on_g _ _ heq')
      case bij =>
        intro z
        rcases g_quotient.surjective z with ⟨x, rfl⟩
        use Quotient.mk S x
        rfl

theorem quotient_of_saturate_closed_image_closed {X Y: Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f: X → Y} (f_cont: Continuous f) (f_surj: Function.Surjective f)
  (h_closed_img_closed: ∀ s: Set X, f ⁻¹' (f '' s) = s → IsClosed s → IsClosed (f '' s)) :
  Topology.IsQuotientMap f := by
    refine Topology.isQuotientMap_iff_isClosed.mpr ?_
    use f_surj
    intro s
    refine Iff.intro ?mp ?mpr
    case mp =>
      exact fun a ↦ IsClosed.preimage f_cont a
    case mpr =>
      intro h_inv_closed
      let t := f ⁻¹' s
      rw [← Set.image_preimage_eq s f_surj]
      exact h_closed_img_closed t Set.preimage_image_preimage h_inv_closed
end
end Chp5


example : (∀ p : (ℕ → Prop), (p 0 ∧ (∀ n: ℕ, (∀ m : ℕ, m ≤ n → p m) → p (n + 1))) → ∀ n, p n) ↔ (∀ p : (ℕ → Prop), (p 0 ∧ (∀ n: ℕ, p n → p (n + 1))) → ∀ n, p n) := by
    constructor
    case mp =>
        intro l
        rintro p ⟨hp0, hp⟩
        apply l
        use hp0
        intro n hn
        apply hp
        apply hn
        exact Nat.le_refl n
    case mpr =>
        intro r
        rintro p ⟨hp0, hp⟩
        have : ∀ n, (∀ m, m ≤ n → p m) := by
            apply r
            constructor
            case a.left =>
                intro m hm
                have : m = 0 := Nat.eq_zero_of_le_zero hm
                rw [this]
                exact hp0
            case a.right =>
                intro n hn
                intro m hm
                have : m ≤ n ∨ m = n + 1 := Nat.le_or_eq_of_le_succ hm
                match this with
                | Or.inl hm_le_n =>
                    apply hn _ hm_le_n
                | Or.inr hm_eq_np1 =>
                    rw [hm_eq_np1]
                    apply hp
                    exact hn
        apply r
        use hp0
        exact fun n a ↦ hp n (this n)

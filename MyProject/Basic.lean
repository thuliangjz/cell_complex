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

theorem cb_boundary_connected {n: ℕ} (hn: 1 < n) : IsConnected (@cb_boundary n) := by
    rw [cb_boundary,←Set.image_univ]
    apply IsConnected.image
    case H =>
        refine connectedSpace_iff_univ.mp ?_
        exact sph_connected hn
    case hf =>
        refine continuous_iff_continuousOn_univ.mp ?_
        exact Isometry.continuous fun x1 ↦ congrFun rfl

end Chp5

-- Coeherent Defs
namespace Chp5
/-the topological space parameter turns out need not be explicit here-/
structure IsCoeherent {X: Type*} [TopologicalSpace X] (B: Set (Set X)) : Prop where
    open_crit: ∀ s : Set X, IsOpen s ↔ ∀ b ∈ B, IsOpen (((↑): b → X)⁻¹' s)
    cover: ⋃₀ B = Set.univ

set_option linter.unusedVariables false in
def CoeherentSigmaMap {X: Type*} [TopologicalSpace X] (B: Set (Set X)) := fun (⟨_, x⟩: Sigma (fun b:B ↦ b.1)) ↦ x.val

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

import YM.RG12.Canonical.Refinement
import YM.OPE.Log.Measuring

/-!
# No filter in the price test (once we extract the actual matrices)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12
open Function Filter Lattice RG Source
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {hC : C.Makes} {φ : Filter UVIndex} [φ.NeBot]
  {M : ∀ d : ℕ, ℕ → RepChart C d}

/-- Price in exactly the currencies in `MatrixTicket`. All indices refer to physical spaces
at this one Table, and `L` is permitted to see only degree `w` and higher via the stated
filtration test. We give the filter-free matrix criterion as two predicates, so it applies
also with restricted degree lists. -/
def RightPrice (C : Family G) (S : Table C.book) (M : ∀ d : ℕ, ℕ → RepChart C d)
    (d : ℕ) : Prop :=
    ∀ x : S.Field d, ∃ p : ℕ, ∀ᶠ k in atTop, ∃ v : C.label d,
      S.project d (M d k v) = x ∧ mass C d v ≤ C.path.levels.clock.hatBeta k ^ p

def RowPrice (C : Family G) (S : Table C.book) (B : DiffPlan S)
    (M : ∀ d : ℕ, ℕ → RepChart C d) (d w : ℕ) : Prop :=
    ∀ L : S.Field d →ₗ[ℂ] ℂ, ∀ h : w ≤ d,
      (∀ e:ℕ, ∀ he:e<w, ∀ x:S.Field e, L (B.rise (he.le.trans h) x)=0) →
      ∃ p : ℕ, ∀ᶠ k in atTop, ∀ v : C.label d,
        ‖L (S.project d (M d k v))‖ ≤
          C.path.levels.clock.hatBeta k^p / C.S.a k^(d-w) * mass C d v

/-- Growth on the actual calendar. Do not replace this currency by `Lambda_m`
(log inverse coupling). It is polynomial in inverse coupling (log inverse *length*). -/
theorem hat_grows (hG : G.Simple) : Tendsto C.path.levels.clock.hatBeta atTop atTop :=
  tendsto_atTop_add_const_left atTop _ (C.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))

variable (hG : G.Simple) (h : Observing C hC φ M)

include h hG
lemma satisfies_matrix_ticket (S : Table C.book) (B : DiffPlan S) :
    OPE.Log.MatrixTicket (C:=C) S B φ ↔
      (∀ d, RightPrice C S M d) ∧ (∀ d w, RowPrice C S B M d w) := by
  refine ⟨fun hu => ⟨?_,?_⟩, fun ⟨hin,hout⟩ => ⟨?_,?_⟩⟩
  · intro d x
    obtain ⟨p,hp⟩ := hu.inlet d (S.representative d x)
    refine ⟨p,?_⟩; filter_upwards [eventually_ge_atTop (C.ref d),hp] with k hk hi
    rw [S.rep] at hi
    exact (h.characterize S d k hk le_rfl x _).1 hi
  · intro d w L hw hl
    obtain ⟨p,hp⟩ := hu.outlet d w L hw hl
    refine ⟨p,?_⟩; filter_upwards [eventually_ge_atTop (C.ref d),hp] with k hk hi
    intro x; obtain ⟨q,hq,hx⟩ := h.purchase d k hk le_rfl x
    exact hi φ le_rfl q _ _ hx hq
  · intro d x
    obtain ⟨p,hp⟩ := hin d (S.project d x)
    refine ⟨p,?_⟩; filter_upwards [eventually_ge_atTop (C.ref d),hp] with k hk hi
    exact (h.characterize S d k hk le_rfl _ _).2 hi
  · intro d w L hw hl
    obtain ⟨p,hp⟩ := hout d w L hw hl
    refine ⟨p,?_⟩; filter_upwards [eventually_ge_atTop (C.ref d),hp,
      (hat_grows (C:=C) hG).eventually_ge_atTop 0] with k hk hi hz
    intro u hu heb q x z hB hx
    obtain ⟨v,rfl,hv⟩ := h.value d k hk heb q x z hB hx
    specialize hi v; exact hi.trans (mul_le_mul_of_nonneg_left hv (div_nonneg (pow_nonneg hz _) (pow_nonneg (C.S.a_pos _).le _)))
omit h [φ.NeBot] in

/-- No NeBot or diagonalization tasks remain if one can price the limiting matrices
independently of the subextraction. -/
theorem matrix_ticket_from_limits (S : Table C.book) (B : DiffPlan S) (f : Extraction.Order)
    (hC : C.Makes)
    (h : ∀ (φ : Filter UVIndex) [φ.NeBot], φ ≤ f.fuse → ∀ M, Observing C hC φ M →
      (∀ d, RightPrice C S M d) ∧ (∀ d w, RowPrice C S B M d w)) :
    ∃ φ : Filter UVIndex, φ.NeBot ∧ φ ≤ f.fuse ∧ OPE.Log.MatrixTicket (C:=C) S B φ := by
  obtain ⟨φ,hφ,he,M,hx⟩ := observe_all C hC (Push.RelayDifference.cutoff_grows f)
  exact ⟨φ,hφ,he,(satisfies_matrix_ticket hG hx S B).2 (h φ he M hx)⟩
end YM.RG12

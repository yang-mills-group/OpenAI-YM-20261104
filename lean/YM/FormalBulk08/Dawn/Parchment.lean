import YM.Planned.PRIMARY_INTEGRAL_295.RollFilm
import Mathlib.Topology.ContinuousMap.Compact

/-!
# VV: engineering roots with an independent real profile

Addresses always in a fixed compact halo in this supply (all starting
letters at zero, include every preimage ancestor); no assumption they
are fixed under a step. `Studio` retains all values including derivatives
through fixed test order. Scalar covariant calculations can operate on
individual real profiles with coefficient norms uniform on this Banach-type
budget; elsewhere we give the polarity to address-measure costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Dawn
open Function Filter Set Lattice
open scoped Topology ContDiff Classical BigOperators

abbrev Pier := ↥(Metric.closedBall (0:E4) 8)
instance compactPier : CompactSpace Pier := isCompact_iff_compactSpace.mp (isCompact_closedBall ..)
def origin : Pier:= ⟨0,by simp⟩
instance : Nonempty Pier := ⟨origin⟩
lemma still (x : Pier) : ‖x.val‖≤8 := by simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
/-- All ordered mixed partial words, redundancy allowed only in this norm. -/
abbrev Brush (D : ℕ) := Σ j:Fin (D+1), (Fin j.val → Axis)
abbrev Panel (D : ℕ) := Brush D→ C(Pier,ℝ)

def garden (D : ℕ) : Submodule ℝ (E4 →ℝ) where
  carrier := {f | ContDiff ℝ D f}
  zero_mem' := (contDiff_const (c:= (0:ℝ)) : ContDiff ℝ D (fun _:E4=> (0:ℝ)))
  add_mem' {f g} (h : ContDiff ℝ D f) (k : ContDiff ℝ D g) := h.add k
  smul_mem' a f (h : ContDiff ℝ D f) := h.const_smul a
abbrev Garden (D : ℕ) := ↥(garden D)

variable {D : ℕ}
lemma tends (f : Garden D) (k:Fin (D+1)) : ContDiff ℝ k.val f.val :=
    (show ContDiff ℝ D f.val from f.property).of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ k.isLt))
def halo (f : Garden D) (b : Brush D) (x : E4) := iteratedFDeriv ℝ b.1.val f.val x (basis ∘ b.2)
lemma haloes (f : Garden D) (b : Brush D) : Continuous (halo f b) :=
    (continuous_eval_const _).comp ((tends f b.1).continuous_iteratedFDeriv le_rfl)

def drawing (D : ℕ) : Garden D→ₗ[ℝ]Panel D where
    toFun f b := ⟨fun x=>halo f b x.val,(haloes f b).comp continuous_subtype_val⟩
    map_add' := by
       intro f g; ext1 b; ext1 x
       change iteratedFDeriv ℝ b.1.val (f.val+g.val) _ _= halo f _ _ + _
       rw [iteratedFDeriv_add_apply (tends f b.1).contDiffAt (tends g b.1).contDiffAt];rfl
    map_smul' := by
       intro a f; ext1 b; ext1 x
       change iteratedFDeriv ℝ b.1.val (a • f.val) _ _ = a * halo f _ _
       rw [iteratedFDeriv_const_smul_apply (tends f b.1).contDiffAt]; rfl

def studio (D : ℕ) := (drawing D).range
abbrev Studio (D : ℕ) := ↥(studio D)

/-- No completeness asserted for Studio; linear evaluations *on* Studio form
a Banach space. -/
abbrev Gallery (D : ℕ) := Studio D→L[ℝ]ℝ

def portrait (D : ℕ) : Garden D→ₗ[ℝ]Studio D := (drawing D).rangeRestrict
lemma portrayed (D:ℕ): Surjective (portrait D) := LinearMap.surjective_rangeRestrict _

lemma le_panel (T:Studio D)(k:Brush D)(x : Pier) : ‖T.val k x‖ ≤ ‖T‖ := ((T.val k).norm_coe_le_norm x).trans (norm_le_pi_norm ..)
lemma panel_le (T: Studio D) {A : ℝ} (hA : 0≤A) (h : ∀ k (v : Pier), ‖T.val k v‖ ≤ A) : ‖T‖≤ A :=
    (pi_norm_le_iff_of_nonneg hA).mpr (fun k: Brush D=> (ContinuousMap.norm_le _ hA).mpr (h k))

def assess (b: Brush D)(p:Pier) : Gallery D := LinearMap.mkContinuous (σ:=RingHom.id ℝ) {
     toFun := fun T: Studio D=> T.val b p,
     map_add' := fun _ _=> rfl,map_smul':=fun _ _=>rfl } 1 (fun f=> by simpa using le_panel f b p)
lemma appraisal (b:Brush D)(x:Pier) (p:Studio D) : ‖assess b x p‖≤‖p‖ := le_panel p b x
lemma appraisal_word (b:Brush D)(x:Pier) (f:Garden D) : assess b x (portrait D f)=halo f b x := rfl
end YM.FormalBulk08.Dawn

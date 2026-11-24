import YM.Integration.WilsonReflectedPublicGuardedColumns
import YM.Integration.WilsonOriginalAlternativeTrialSource
/-! The guarded engineering source at the true K pin after the actual rotation
and optional conjugation, including its genuine failed healthy-support mask. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicGuardedMotion
open Function Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Planned.GuardedAtom MergeProof Push Push.Local PhysicalNext.Repeat.Legato
open WilsonReflectedFundedHearing WilsonOriginalAlternativeTrialSource
open scoped Classical BigOperators
variable {G:Gauge} {d:ℕ} {n:Side} {F:Frame G d} {T:SectionData F}
  {H:Hol G} (Z:Rep G n)

theorem faced (sound:T.Sound H) (w:F.Coeff)(t:Signed)(c:Site n)(U:Config G n):
    part T c Z U (F.act t.ortho w)=part T 0 Z (pull t c U) w := by
  have he:=footprint_turn sound t (0:Site n) c
  have moved:affine t c (0:Site n)=c:=by simp [affine]
  have hP (v:F.Coeff):T.places v 0 ∘ pull t c = T.places (F.act t.ortho v) (affine t c 0):=
    funext fun V=>T.placed_signed sound t 0 c v V
  have raw:part T (affine t c 0) Z U (F.act t.ortho w)=part T 0 Z (pull t c U) w:=by
    simp only [Extra.Histories.part,LinearMap.coe_mk,AddHom.coe_mk]
    rw [act_at_zero,←core_act,F.scaling,he,masked_pull,hP]
    rfl
  simpa only [moved] using raw

theorem barred (sound:T.Sound H) (w:F.Coeff)(c:Site n)(U:Config G n):
    part T c Z U (star w)=star (part T c Z U w) := by
  simp only [Extra.Histories.part,LinearMap.coe_mk,AddHom.coe_mk]
  rw [Pi.star_apply,star_add,core_star,scaled_star,
    show T.places (star (F.scaled Z.p.threshold⁻¹ (F.core w))) c =
      star (T.places (F.scaled Z.p.threshold⁻¹ (F.core w)) c) from funext fun _=>sound.ordinary_real ..,
    masked_bar]

variable (R:Run G){N p f K:ℕ}
local notation "C₀" => R.family
local notation "P₀" => (C₀).path.rep N p K
local notation "F₀" => (C₀).labels.level d

def coords (A:Arm R d N p f K): (C₀).label d := Motion.patch (F₀) (A.s,A.b) A.w

theorem placed (A:Arm R d N p f K)(h:f≤K) (U:Config G ((C₀).side K p)):
    WilsonReflectedFundedHearing.cropped R A h U=(((C₀).S.a K:ℂ)^d)⁻¹*
      part ((C₀).localSection d) (((C₀).S.toDepth h p).embed A.o) (P₀) U (coords R A) := by
  let c:=((C₀).S.toDepth h p).embed A.o
  have turned:part ((C₀).localSection d) c (P₀) U (((C₀).labels.level d).act A.s.ortho A.w) =
      part ((C₀).localSection d) 0 (P₀) (pull A.s c U) A.w :=
    faced (F:=(C₀).labels.level d) (P₀) (R.makes.sections d) A.w A.s c U
  change _ * RelayDifference.hand A.b (part _ 0 (P₀) (pull A.s c U) A.w) = _ *
    part ((C₀).localSection d) c (P₀) U (coords R A)
  apply congrArg (fun x:ℂ => (((C₀).S.a K:ℂ)^d)⁻¹ * x)
  rw [←turned]
  cases h:A.b
  · simp [coords,Motion.patch,h,RelayDifference.hand]
  · simp only [coords,Motion.patch,h,if_true,RelayDifference.hand]
    exact (barred (P₀) (R.makes.sections d) _ c U).symm

end YM.Integration.WilsonReflectedPublicGuardedMotion
end

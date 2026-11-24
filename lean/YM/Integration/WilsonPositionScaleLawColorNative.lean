import YM.Integration.WilsonPhysicalPositionAdmissible
import YM.Integration.WilsonMeasuredPublicEntranceActionTests

/-! Each admitted position-coordinate candidate acts on the original labels
with the four native properties and preserves all recorded free tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorNative
open Function Filter Set Spec Table Extraction OPE Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open XSpace XSpace.Stab XSpace.Normalize
open WilsonPhysicalPositionAdmissible (Native)
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPhysicalPositionBornTransition (present)
open WilsonPhysicalPositionBornCandidates (possible)
open WilsonMeasuredPublicEntranceCommonColor (carried)
open WilsonMeasuredPublicEntranceFiniteFreeTests (Hearing heard)
open scoped Topology Classical
variable {G : Gauge} (C : Family G) {d : ℕ}
private abbrev L (C : Family G) (d : ℕ) := (Bel C.book).Field d

theorem enrolled (a : MoveSpace G d) (v : L C d) :
    fields C.labels d (present (C:=C) (field a) v) = field a (fields C.labels d v) :=
  (fields C.labels d).apply_symm_apply _

theorem lifted (a : MoveSpace G d) : carried C (present (C:=C) (field a)) = field a := by
  ext1 p
  change fields C.labels d (present (C:=C) (field a) ((fields C.labels d).symm p)) = _
  rw [enrolled,LinearEquiv.apply_symm_apply]

theorem native (a : MoveSpace G d) : Native C (present (C:=C) (field a)) := by
  let U := fields C.labels d
  let K := (guide G d).symm a
  have unit : U (WilsonPhysicalPositionAdmissible.unit C d) = leaf G d := Subtype.ext (unit_address ..)
  have star (v : L C d) : U (WilsonPhysicalPositionAdmissible.real C d v) = reel d (U v) :=
    Subtype.ext (address_star ..)
  have face (s : Signed) (v : L C d) : U (WilsonPhysicalPositionAdmissible.turns C d s v) =
      ori s.ortho d (U v) := Subtype.ext (address_motion ..)
  refine ⟨?_,?_,?_,?_⟩
  · apply U.injective
    rw [show U (present (C:=C) (field a) _) = _ from enrolled C a _,unit]
    exact solitary K
  · intro j hj v
    let x := U ((scheme C.labels).rise hj v)
    have hx : x.val = (fields C.labels j v).val := by
      change address C.labels d ((scheme C.labels).rise hj v) = address C.labels j v
      rw [address_rise]
    have small : x.val ∈ shellSector G j := hx ▸ (fields C.labels j v).property
    have member : (field a x).val ∈ shellSector G j :=
      Submodule.add_mem _ small (K.property.2.1 j hj x small)
    let w : Sec G j := ⟨(field a x).val,member⟩
    refine ⟨(fields C.labels j).symm w,?_⟩
    apply address_inj C.labels d
    rw [address_rise,address_eval,address_eval,LinearEquiv.apply_symm_apply,enrolled]
  · intro v
    apply U.injective
    calc U (present (C:=C) (field a) (WilsonPhysicalPositionAdmissible.real C d v)) =
          field a (reel d (U v)) := (enrolled C a _).trans (congrArg (field a) (star v))
      _ = reel d (field a (U v)) := by
        change reel d (U v) + K.val (reel d (U v)) = reel d (U v + K.val (U v))
        rw [K.property.2.2.1,map_add]
      _ = _ := (congrArg (reel d) (enrolled C a v).symm).trans (star _).symm
  · intro s v
    apply U.injective
    calc U (present (C:=C) (field a) (WilsonPhysicalPositionAdmissible.turns C d s v)) =
          field a (ori s.ortho d (U v)) := (enrolled C a _).trans (congrArg (field a) (face s v))
      _ = ori s.ortho d (field a (U v)) := by
        change ori s.ortho d (U v) + K.val (ori s.ortho d (U v)) = ori s.ortho d (U v + K.val (U v))
        rw [K.property.2.2.2,map_add]
      _ = _ := (congrArg (ori s.ortho d) (enrolled C a v).symm).trans (face s _).symm

theorem free {B : ℝ} (a : MoveSpace G d) (chosen : a ∈ possible C d B)
    {I : Type*} (e : Module.Basis I ℂ (Sec G d)) (h : Hearing I) :
    heard e (carried C (present (C:=C) (field a))) h = 0 := by
  rw [lifted]
  exact sub_eq_zero.mpr (congrArg (fun P : Prediction G d => P h.arity h.profile (fun i => e (h.inputs i))) chosen.1)

theorem original (simple : G.Simple) (h : 6 ≤ d) {B : ℝ} (a : MoveSpace G d)
    (chosen : a ∈ possible C d B)
    (cone : ∃ t : ℝ, 0 ≤ t ∧ ∃ k : ℂ,
      present (C:=C) (field a) (WilsonMeasuredPublicEntranceActionColor.field C (by omega : 4≤d)) =
      (t:ℂ) • WilsonMeasuredPublicEntranceActionColor.field C (by omega : 4≤d) + k • (Bel C.book).unit d) :
    ∃ c : Knight G, (conn c 1 ∨ conn c (-1)) ∧
      ∀ p : Sec G d, records G d (field a p) = changing c (records G d p) := by
  obtain ⟨s,n,_,tests⟩ := WilsonMeasuredPublicEntranceActionTests.original C simple h
  obtain ⟨c,branch,all⟩ := tests (present (C:=C) (field a)) (native C a) (fun i _ => free C a chosen _ i) cone
  refine ⟨c,branch,fun p => ?_⟩
  have ok := all ((fields C.labels d).symm p)
  simpa only [enrolled,LinearEquiv.apply_symm_apply] using ok

end YM.Integration.WilsonPositionScaleLawColorNative
end

import YM.Integration.WilsonPhysicalHistoryRegisteredSplit

/-! The older regular observable translated to the genuine deposited point. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionRegisteredTranslate
open Function Lattice RG Wilson Source Labels Push.Local MergeProof
open Extra.Histories WilsonInvariantActionRegisteredTranslate
open private motion from YM.Integration.WilsonTranslatedFactory
open scoped BigOperators Classical
variable {G:Gauge} {C:Family G} (h:C.Makes) {N per k d:ℕ}

theorem original (hk:k≤N) (w:C.label d) (o:Site (C.side k per)) (U:Config G (C.side k per)):
    WilsonInheritedRegisteredField.regular h hk w o U =
      alto C.path k d *
        (((C.factory d N per).entries k ((C.factory d N per).terminal.symm w)).exponentialEntry 0
        (C.localSection d) (C.path.rep N per k) (pull 1 o U)):=by
  let Y:=((C.factory d N per).entries k ((C.factory d N per).terminal.symm w))
  let m:=motion h hk o
  let S:=C.localSection d
  let Q:=C.path.rep N per k
  let F:=C.labels.level d
  have eqn:(reorient m Y).exponentialEntry (affine 1 o 0) S Q =
      Y.exponentialEntry 0 S Q ∘ pull 1 o:=by
    funext V
    have he:=footprint_turn (h.sections d) (1:Signed) (0:Site (C.side k per)) o
    have foot (v): S.places v 0 ∘ pull 1 o = S.places (F.act (1:Signed).ortho v) (affine 1 o 0):=
      funext fun W=>S.placed_signed (h.sections d) 1 0 o v W
    unfold Coefficient.exponentialEntry Coefficient.maskedTerm reorient
    dsimp only [Function.comp_apply]
    rw [act_at_zero,←core_act,F.scaling,he,masked_pull,foot]
    simp only [masked_pull]
    rfl
  change (alto C.path k d)*(reorient m Y).exponentialEntry o S Q U=_
  exact congrArg (fun z:ℂ=>alto C.path k d*z) (by simpa only [Function.comp_apply,affine,Signed.act_zero,zero_add] using congrFun eqn U)

end YM.Integration.WilsonInvariantActionRegisteredTranslate

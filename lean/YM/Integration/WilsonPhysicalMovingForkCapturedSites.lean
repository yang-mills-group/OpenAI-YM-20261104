import YM.Integration.WilsonOriginalTwoFlatGrid
import YM.Integration.WilsonMovingForkPrintedFile

/-! The occupied addresses of the actual planted K board at the common physical capture. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalMovingForkCapturedSites
open Function Filter Set Lattice RG Wilson Next.Rank Source OPE MergeProof
open Trace.Physical.GermGraph Trace.Pilot PhysicalNext PhysicalNext.Repeat.Legato Ribbons Accent Cells Extra.Histories RG16 RG16.Literal
open WilsonMovingForkPrintedFile (parent)
open WilsonMovingForkSeededPoint (seats)

theorem original {G:Gauge}(R:Run G){c f K n:ℕ}(cf:c≤f)(fk:f≤K)(per:ℕ)(sites:Fin n→ Lattice.Cover)
    (insideRoot:∀i,8*‖R.family.S.gridPoint f (sites i)‖≤R.family.S.a (c+1)):
    ∀i,parent R (cf.trans fk) per (seats (R:=R) fk per sites) i=0:=by
  intro i
  let C:=R.family
  have unit:C.S.a (c+1)≤1:=(C.S.strictAnti.antitone (Nat.zero_le _)).trans_eq C.S.a_zero
  have small:‖C.S.gridPoint f (sites i)‖≤1:=by linarith only [insideRoot i,unit]
  have position:C.S.place (seats (R:=R) fk per sites i)=C.S.gridPoint f (sites i):=by
    unfold seats
    rw [C.S.embeds_place]
    exact inside C f per small
  have tent:2*‖C.S.place (seats (R:=R) fk per sites i)‖≤C.S.a c:=by
    rw [position]
    exact (by linarith only [insideRoot i,norm_nonneg (C.S.gridPoint f (sites i))] :
      2*‖C.S.gridPoint f (sites i)‖≤C.S.a (c+1)).trans (C.S.strictAnti.antitone (Nat.le_succ c))
  have zero:=Frontier6.Road.loops_zero C per K c (seats (R:=R) fk per sites i) (cf.trans fk) tent
  exact (vote C K per c (seats (R:=R) fk per sites i) (cf.trans fk)).symm.trans zero

end YM.Integration.WilsonPhysicalMovingForkCapturedSites
end

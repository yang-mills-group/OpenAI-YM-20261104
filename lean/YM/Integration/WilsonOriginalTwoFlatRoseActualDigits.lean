import YM.Integration.WilsonOriginalTwoFlatRoseFixedFiles
import YM.Integration.WilsonReceivedChronologicalMaterialApertures
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseActualDigits
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G){f K N per j:ℕ}

open WilsonReceivedChronologicalMaterialSites (physical footprint)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonOriginalPublicFixedCourse (sites home)
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonCenteredCompactBooking (mass)
open MeasureTheory Filter

theorem child (o:Fin 3→Site (R.family.side f per))(fk:f≤K)(kn:K≤N)(jk:j≤K)(a:Fin 3):
    sites R (N:=N) per j (jk.trans kn) (pin R (fk.trans kn) o) a=
      physical R (pin R fk o) jk a:=by
  let g:=R.family.S.toDepth fk per
  let h:=R.family.S.toDepth kn per
  let k:=R.family.S.toDepth jk per
  let n:=R.family.S.toDepth (fk.trans kn) per
  let p:=R.family.S.toDepth (jk.trans kn) per
  have nest:=Next.Rank.Station.parent_nested k h p (R.family.S.toDepth_odd jk per)
    (R.family.S.toDepth_odd kn per) (n.embed (o a))
  change p.parent (n.embed (o a))=k.parent (g.embed (o a))
  rw [nest,Next.Rank.Station.embed_comp g h n (o a),h.embed_parent]

private theorem at_grid (o:Fin 3→Site (R.family.side f per))(fj:f≤j)(jn:j≤N)(a:Fin 3):
    sites R (N:=N) per j jn (pin R (fj.trans jn) o) a=pin R fj o a:=by
  let g:=R.family.S.toDepth fj per
  let h:=R.family.S.toDepth jn per
  let n:=R.family.S.toDepth (fj.trans jn) per
  change h.parent (n.embed (o a))=g.embed (o a)
  rw [Next.Rank.Station.embed_comp g h n (o a),h.embed_parent]

theorem tape (o:Fin 3→Site (R.family.side f per))(fk:f≤K)(kn:K≤N):
    WilsonOriginalPublicFixedCourse.digits R (N:=N) per (pin R (fk.trans kn) o)=
      WilsonReceivedChronologicalMaterialSites.digits R (pin R fk o):=by
  funext j a
  unfold WilsonOriginalPublicFixedCourse.digits WilsonReceivedChronologicalMaterialSites.digits
  by_cases active:j+1≤K
  · rw [dif_pos active,dif_pos (active.trans kn),child R o fk kn active a]
    rfl
  · rw [dif_neg active]
    by_cases late:j+1≤N
    · rw [dif_pos late,at_grid R o (show f≤j+1 by omega) late]
      have fj:f≤j:=by omega
      let g:=R.family.S.toDepth fj per
      let h:=(R.family.path.levels.clock.op j per).ratio
      let n:=R.family.S.toDepth (show f≤j+1 by omega) per
      change h.residue (n.embed (o a))=0
      rw [Next.Rank.Station.embed_comp g h n (o a),h.residue_embed]
    · rw [dif_neg late]

theorem center (o:Fin 3→Site (R.family.side f per))(fk:f≤K)(kn:K≤N)(jk:j≤K)
    (zero:∀a,physical R (pin R fk o) jk a=0)(a:Fin 3):
    home R (N:=N) per j (jk.trans kn) (pin R (fk.trans kn) o) a=0:=by
  funext i
  change lift (sites R (N:=N) per j (jk.trans kn) (pin R (fk.trans kn) o) a)+
    lift (sites R (N:=N) per j (jk.trans kn) (pin R (fk.trans kn) o) i-
      sites R (N:=N) per j (jk.trans kn) (pin R (fk.trans kn) o) a)=0
  rw [child R o fk kn jk a,child R o fk kn jk i,zero a,zero i]
  funext d
  simp

end YM.Integration.WilsonOriginalTwoFlatRoseActualDigits
end

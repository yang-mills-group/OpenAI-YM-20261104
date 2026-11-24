import YM.Integration.WilsonOriginalTwoFlatRoseHousedDigits
import YM.Integration.WilsonIndependentCollarOrdinaryCruise
import YM.Integration.WilsonOriginalHeterogeneousStopSites
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseCapturedDigits
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

open WilsonOriginalTwoFlatRoseActualDigits (tape center)
open Function Set Filter MeasureTheory Analysis Table Spec Extraction Next.UVStress
open StressFlux.Matching Cells WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking
open WilsonReceivedChronologicalMaterialCapture (pinned)
open WilsonOriginalTwoFlatIRHousing


open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonReceivedChronologicalMaterialSites (digits footprint)
open WilsonOriginalTwoFlatRoseHousedDigits (marks)

private theorem zero_address {L:Levels G}{cells:Digits L (Fin 3)}(len v:ℕ)
    (zero:∀j,v≤j→j<v+len→cells j=0):address L cells len v 0=0:=by
  induction len generalizing v with
  | zero=>rfl
  | succ d ih=>
    rw [WilsonIndependentCollarOrdinaryCruise.address,zero v le_rfl (by omega)]
    have head:chartIn (loose L v) (0:Fin 3→Lattice.Cover) 0=0:=by
      funext i e
      simp [chartIn]
    rw [head]
    exact ih (v+1) fun j lo hi=>zero j (by omega) (by omega)

def Rolled (o:Fin 3→Site (R.family.side f per))(fk:f≤K)(kn:K≤N){v c:ℕ}(vc:v+1≤c)(ck:c≤K):Prop:=
  let P:=pin R fk o
  WilsonOriginalPublicFixedCourse.digits R (N:=N) per (pin R (fk.trans kn) o)=digits R P ∧
    ∀anchor:Fin 3,home R (N:=N) per c (ck.trans kn) (pin R (fk.trans kn) o) anchor=
      address R.family.path.levels (digits R P) (c-(v+1)) (v+1) (footprint R P (vc.trans ck))

theorem purchased (o:Fin 3→Site (R.family.side f per))(fk:f≤K)(kn:K≤N){v c:ℕ}(vc:v+1≤c)(ck:c≤K)
    (housed:∀j,∀jc:j≤c,∀a,physical R (pin R fk o) (jc.trans ck) a=0):Rolled R o fk kn vc ck:=by
  refine ⟨tape R o fk kn,?_⟩
  intro anchor
  rw [center R o fk kn ck (housed c le_rfl)]
  have small:footprint R (pin R fk o) (vc.trans ck)=0:=by
    funext a e
    simp [footprint,housed (v+1) vc a,lift]
  rw [small]
  symm
  apply zero_address
  intro j lo hi
  have atC:j+1≤c:=by omega
  funext a
  let g:=(R.family.path.levels.clock.op j per).ratio
  change (if h:j+1≤K then g.residue (physical R (pin R fk o) h a) else 0)=0
  rw [dif_pos (atC.trans ck),housed (j+1) atC a,←g.root.map_zero]
  exact g.residue_embed 0

theorem positioned (o:Fin 3→Lattice.Cover)(fk:f≤K)(kn:K≤N){v c:ℕ}(vc:v+1≤c)(ck:c≤K)
    {B r:ℝ}(size:∀a,‖R.family.S.gridPoint f (o a)‖≤B*r)(room:4*(B*r)<R.family.S.a c):
    Rolled R (marks R (f:=f) (per:=per) o) fk kn vc ck:=by
  apply purchased
  intro j jc a
  have pay:=WilsonOriginalHeterogeneousStopSites.funded R (p:=per) fk (jc.trans ck) o (0:Fin 3) size
    (room.trans_le (R.family.S.strictAnti.antitone jc)) a
  change (R.family.S.toDepth (jc.trans ck) per).parent ((R.family.S.toDepth fk per).embed (wrap _ (o a-o 0)))=0
  exact (show (R.family.S.toDepth fk per).embed (wrap _ (o a-o 0))=
    (R.family.S.toDepth fk per).embed (wrap _ (o a))-(R.family.S.toDepth fk per).embed (wrap _ (o 0)) from by
    rw [Ratio.embed_wrap,Ratio.embed_wrap,Ratio.embed_wrap,smul_sub,map_sub]) ▸ pay

theorem original (φ:Test 3):
    ∃scale:ℝ,∃pos:0<scale,∀r:ℝ,0<r→scale*r≤R.family.S.a 0 →
    let b:=WilsonCloseCaptureDate.level R.family.S (scale*r)
    ∀(v c f K N per:ℕ)(vc:v+1≤c)(cb:c≤b)(bf:b≤f)(fk:f≤K)(kn:K≤N),
    8*R.family.S.a f<R.family.S.a b →
    ∀z:Sites R (f,per) 3,WilsonCenteredCompactBooking.mass R φ r (f,per) z≠0 →
      WilsonCenteredCompactBooking.mass R (dilate (inv_pos.mpr pos) φ) (scale*r) (f,per) z=
        WilsonCenteredCompactBooking.mass R φ r (f,per) z ∧ Rolled R z fk kn vc (cb.trans (bf.trans fk)):=by
  obtain ⟨scale,pos,finance⟩:=WilsonReceivedChronologicalMaterialApertures.original R φ
  refine ⟨scale,pos,?_⟩
  intro r posR small b v c f K N per vc cb bf fk kn width z active
  obtain ⟨mass,_foot,pins⟩:=finance r posR small v f K per (vc.trans cb) bf fk width z active
  exact ⟨mass,purchased R z fk kn vc (cb.trans (bf.trans fk)) (fun j jc=>pins j (jc.trans cb))⟩

end YM.Integration.WilsonOriginalTwoFlatRoseCapturedDigits

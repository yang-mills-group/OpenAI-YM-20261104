import YM.Integration.WilsonOriginalTwoFlatRoseActualDigits
import YM.Integration.WilsonOriginalHeterogeneousStopSites
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseHousedDigits
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

def marks (o:Fin 3 → Lattice.Cover):Fin 3→Site (R.family.side f per):=fun i=>wrap _ (o i-o 0)

def Joined (o:Fin 3→Site (R.family.side f per))(fk:f≤K)(kn:K≤N){m:ℕ}(start:m+1≤K):Prop:=
  WilsonOriginalPublicFixedCourse.digits R (N:=N) per (pin R (fk.trans kn) o)=
      WilsonReceivedChronologicalMaterialSites.digits R (pin R fk o) ∧
  ∀anchor:Fin 3,home R (N:=N) per (m+1) (start.trans kn) (pin R (fk.trans kn) o) anchor=
      footprint R (pin R fk o) start

theorem purchased (o:Fin 3→Site (R.family.side f per))(fk:f≤K)(kn:K≤N){m:ℕ}(start:m+1≤K)
    (flat:∀a,physical R (pin R fk o) start a=0):Joined R o fk kn start:=by
  refine ⟨tape R o fk kn,?_⟩
  intro anchor
  rw [center R o fk kn start flat]
  funext a
  change 0=lift (physical R (pin R fk o) start a)
  rw [flat a]
  funext d
  simp [lift]

theorem positioned (o:Fin 3 → Lattice.Cover)(fk:f≤K)(kn:K≤N){m:ℕ}(start:m+1≤K)
    {M r:ℝ}(size:∀a,‖R.family.S.gridPoint f (o a)‖≤M*r)(room:4*(M*r)<R.family.S.a (m+1)):
    Joined R (marks R (f:=f) (per:=per) o) fk kn start:=by
  apply purchased R _ fk kn start
  intro a
  have pay:=WilsonOriginalHeterogeneousStopSites.funded R (p:=per) fk start o (0:Fin 3) size room a
  change (R.family.S.toDepth start per).parent ((R.family.S.toDepth fk per).embed (wrap _ (o a-o 0)))=0
  exact (show (R.family.S.toDepth fk per).embed (wrap _ (o a-o 0))=
    (R.family.S.toDepth fk per).embed (wrap _ (o a))-(R.family.S.toDepth fk per).embed (wrap _ (o 0)) from by
    rw [Ratio.embed_wrap,Ratio.embed_wrap,Ratio.embed_wrap,smul_sub,map_sub]) ▸ pay

theorem original (φ:Test 3):
    ∃scale:ℝ,∃positive:0<scale,∀r:ℝ,0<r → scale*r ≤ R.family.S.a 0 →
    let b:=WilsonCloseCaptureDate.level R.family.S (scale*r)
    ∀(m f K N per:ℕ)(_:m+1≤b)(_:b≤f)(_:f≤K)(_:K≤N),
    8*R.family.S.a f<R.family.S.a b →
    ∀z:Sites R (f,per) 3,WilsonCenteredCompactBooking.mass R φ r (f,per) z≠0 →
      WilsonCenteredCompactBooking.mass R (dilate (inv_pos.mpr positive) φ) (scale*r) (f,per) z=
        WilsonCenteredCompactBooking.mass R φ r (f,per) z ∧
      ∀(fk:f≤K)(kn:K≤N)(start:m+1≤K),Joined R z fk kn start:=by
  obtain ⟨scale,pos,h⟩:=WilsonReceivedChronologicalMaterialApertures.original R φ
  refine ⟨scale,pos,?_⟩
  intro r rp small b m f K N per early old fine live narrow z active
  obtain ⟨money,_unit,roots⟩:=h r rp small m f K per early old fine narrow z active
  refine ⟨money,?_⟩
  intro fk kn start
  exact purchased R z fk kn start (roots _ early)

end YM.Integration.WilsonOriginalTwoFlatRoseHousedDigits
end

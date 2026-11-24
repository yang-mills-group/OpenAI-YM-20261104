import YM.Integration.WilsonNeutralTwoPrintPathCopies
import YM.Integration.WilsonReceivedDepositedOrbitalHearing

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalPrint
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
variable {G:Gauge}{n e j:ℕ}{k D:Fin n → ℕ}{S J:Finset (Fin n)}{A δ σ:ℝ}
variable (R:Run G)(Y:Realm G (e+1) Credit.leanC)(lo:Y.anchor ≤ j)(enrolled:Paid R Y lo D k δ σ)
variable (N:ℕ) (c:Fin n)(X:Input Y lo S k D A)(included:J⊆S)(pin:c∈J)(positive:0 ≤ A)
variable (older:j<N)(deep:0 < mass k J)(sw:0 ≤ σ)(o:Cover)(t:Case D)(u:Frill J c)

open PowerSeries WilsonCoeffUV.Blue
open WilsonReceivedCompactVerseEntrance
open WilsonReceivedCoverGrade (Same)
open WilsonNeutralTwoPrintPathCopies (chart)

def front (y:Fin n→ Cover):Frill J c:=fun p=>y p.val

theorem seated (y:Fin n→ Cover)(v:Fin n)(inJ:v∈J):
    toe J c (y c) (front (J:=J) c y) v=y v:=by
  by_cases h:v=c
  · subst v
    exact toeO .. 
  · have active:v∈J.erase c:=mem_erase.mpr ⟨h,inJ⟩
    simp only [toe,if_neg h,dif_pos active,front]

include enrolled included pin positive older in
theorem original (old:Outerm G D)(well:Wellness k old){s B:ℝ}(hs:0<s)(hB:1≤B)
    (cover:CoverBill old e s B)(bound:∀y J,Same e (output X J N y) (old y J))
    (y:Fin n→ Cover)(n':Side)(x:Site n')(a:ℕ)(through:a≤e)(r:ℕ)(z:Fin r→Woods G n'):
    chart Y lo N c X (y c) t (front (J:=J) c y) n' x a r z=
      pPly t J (((submit old k e) y J).1 n') a r (jog (-(x-wrap n' (y c))) ∘z):=by
  let u:=front (J:=J) c y
  have roots:old (toe J c (y c) u) J=old y J:=well.filial _ _ J (seated c y)
  have kept:=bound (toe J c (y c) u) J a through
  rw [roots] at kept
  have high:=(WilsonOlderFreshConnectedBinding.filed R Y lo enrolled N c X included pin positive older
    (y c) u a through).2.2 n' r
  have low:=((WilsonReceivedCompactVerseEntrance.original old well hs hB cover).2.2.1 y J a through).2 n' r
  rw [kept] at high
  exact congrArg (touch t J) (congrFun (high.trans low.symm) (jog (-(x-wrap n' (y c))) ∘z))

include enrolled included pin positive older in
theorem centered (old:Outerm G D)(well:Wellness k old){s B:ℝ}(hs:0<s)(hB:1≤B)
    (cover:CoverBill old e s B)(bound:∀y J,Same e (output X J N y) (old y J))
    (y:Fin n→ Cover)(n':Side)(a:ℕ)(through:a≤e):
    coeff a (flash (chart Y lo N c X (y c) t (front (J:=J) c y) n' (wrap n' (y c))))=
      coeff a (readO t ((submit old k e) y J) n'):=by
  have sides: chart Y lo N c X (y c) t (front (J:=J) c y) n' (wrap n' (y c)) a=
      pPly t J (((submit old k e) y J).1 n') a:=by
    funext r z
    rw [original R Y lo enrolled N c X included pin positive older t old well hs hB cover bound y n' (wrap n' (y c)) a through r z]
    have back:jog (0:Site n') ∘ z =z:=by
      funext v
      exact Prod.ext (zero_add _) rfl
    simp only [sub_self,neg_zero,back]
  change coeff a (PowerSeries.mk (fun l=>totalR (chart Y lo N c X (y c) t (front (J:=J) c y) n' (wrap n' (y c)) l)))=_
  simpa only [readO,Blue.flash,coeff_mk] using congrArg totalR sides

end YM.Integration.WilsonReceivedDepositedOrbitalPrint
end

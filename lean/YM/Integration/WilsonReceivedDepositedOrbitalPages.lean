import YM.Integration.WilsonReceivedDepositedOrbitalRay

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalPages
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
variable {G:Gauge}{n e i:ℕ}{k D:Fin n → ℕ}{S J:Finset (Fin n)}{A δ σ:ℝ}
variable (R:Run G)(Y:Realm G (e+1) Credit.leanC)(lo:Y.anchor ≤ i+1)(enrolled:Paid R Y lo D k δ σ)
variable (N:ℕ) (c:Fin n)(X:Input Y lo S k D A)(included:J⊆S)(pin:c∈J)(positive:0 ≤ A)
variable (older:i+1<N)(deep:0 < mass k J)(sw:0 ≤ σ)(o:Cover)(t:Case D)(u:Frill J c)

open PowerSeries WilsonCoeffUV.Blue
open WilsonReceivedCompactVerseEntrance
open WilsonReceivedCoverGrade (Same)
open WilsonNeutralTwoPrintPathCopies (chart)


open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonOriginalPrimerReplicatedInk (located)
open WilsonVacuumPreResetStationaryChange
open WilsonOriginalChargedForestQ
open WilsonOriginalFoldedMarkedRightColumn (before)
open WilsonReceivedDepositedSocketRows (entered)
open Further.PhysicalPeriodLimitF933 Shingle FVA1Physical.TwoReset


open private carry from YM.Integration.WilsonReceivedDepositedOrbitalRay

def offered (old:Outerm G D)(k:Fin n→ℕ)(e:ℕ)(y:Fin n → Cover)(t:Case D)(J:Finset (Fin n))
    (c:Fin n)(n':Side)(x:Site n'):PChart G n':=
  skewV (x-wrap n' (y c)) (pPly t J (((submit old k e) y J).1 n'))

include enrolled included pin positive older in
theorem jets (old:Outerm G D)(well:Wellness k old){s B:ℝ}(hs:0<s)(hB:1≤B)
    (cover:CoverBill old e s B)(bound:∀y J,Same e (output X J N y) (old y J))
    (y:Fin n → Cover){n' f:Side}(h:n'.val∣f.val)(site:Site n')(a:ℕ)(through:a≤e):
    coeff a (flash (located h site (chart Y lo N c X (y c) t (front (J:=J) c y) f)))=
      coeff a (flash (located h site (offered old k e y t J c f))):=by
  have lenses v:=WilsonReceivedDepositedOrbitalPrint.original R Y lo enrolled N c X included pin positive
    older t old well hs hB cover bound y f (page h site v).val a through
  have rows:(located h site (chart Y lo N c X (y c) t (front (J:=J) c y) f)) a=
      (located h site (offered old k e y t J c f)) a:=by
    funext r z
    simp only [located,Finset.sum_apply]
    exact Finset.sum_congr rfl fun v _=>lenses v r z
  simpa only [Blue.flash,coeff_mk] using congrArg totalR rows

include enrolled included pin positive older in
theorem original (old:Outerm G D)(well:Wellness k old){s B:ℝ}(hs:0<s)(hB:1≤B)
    (cover:CoverBill old e s B)(bound:∀y J,Same e (output X J N y) (old y J))
    (y:Fin n → Cover)(per:ℕ)(F:Forest (step R i per).ratio){n':Side}(h:n'.val∣(fine R i per).val)
    (site:Site n')(a:ℕ)(through:a≤e):
    let f:=fine R i per
    coeff a (before R N i per (by omega) F (located h site (chart Y lo N c X (y c) t (front (J:=J) c y) f)))=
      coeff a (before R N i per (by omega) F (located h site (offered old k e y t J c f))):=by
  dsimp only
  let K:=model R N i per (show i<N by omega)
  let L:=SignedMeasuredSourceSeries.probe (step R i per) F (saddle R N i per F) (fderiv ℝ (K.b F) 0)
  change coeff a (L (flash _))=coeff a (L (flash _))
  apply carry L _ (d:=e) _ a through
  · dsimp only [L]
    rw [SignedMeasuredSourceSeries.genuine]
    exact WilsonCoeffUV.Blue.train_X _
  · exact jets R Y lo enrolled N c X included pin positive older t old well hs hB cover bound y h site

end YM.Integration.WilsonReceivedDepositedOrbitalPages
end

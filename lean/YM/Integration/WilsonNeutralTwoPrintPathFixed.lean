import YM.Integration.WilsonCapturedPrimaryWeakTrialFixedInput
import YM.Integration.WilsonReceivedFixedDigitCanonical

/-! The lower native print and the independently declared fixed-digit trial
use the same original raw socket at its actual birth. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace YM.Integration.WilsonNeutralTwoPrintPathFixed
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
open IndependentSourcePathFamily OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds WilsonCoeffUV.Winding
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCompactVerseEntrance (CoverBill)
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Carp XSpace
variable {G:Gauge}{n e j:ℕ}{d h:Fin n→ℕ}(R:Run G)
variable (κ:(v:Fin n)→Knob (h v))(pt:Fin n→Chamber)


open Function Filter Finset Lattice Wilson RG Precision Laurent WilsonCoeffUV Tree Bloch Exterior
open WilsonReceivedFixedDigitHistory (Digits itinerary)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonCapturedPrimaryWeakTrialFixedInput (places)

def parcel {L:Levels G}(same:L=R.family.path.levels)(cells:Digits R.family.path.levels (Fin n)):Digits L (Fin n):=
  same.symm ▸ cells

theorem birth {L:Levels G}{O:ChartRatio G}(same:L=R.family.path.levels)(scheme:O=R.metals.O)
    (cells:Digits R.family.path.levels (Fin n))(N j:ℕ)(q:(v:Fin n)→Choice R d v)(y:Fin n → Cover)(J:Finset (Fin n)):
    logO L O j N (start R d κ pt q (chartIn (loose L j) y (parcel R same cells j))) d J=
      fixed R d κ pt N (j+1) j cells q y J:=by
  subst L
  subst O
  simp only [WilsonReceivedFixedDigitCanonical.fixed,Nat.add_sub_cancel_left]
  rfl

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ):
    ∃A:ℝ,1≤A ∧ ∀ᶠj:ℕ in Filter.atTop,∃ν B:ℝ,0<ν ∧ 1≤B ∧
    ∀(Y:Realm G (e+1) Credit.leanC)(lo:Y.anchor≤j)(same:Y.draws=R.family.path.levels),Y.paid=R.metals.O →
      (Y.mint (j+1) (by omega)).σ≤1 → ∀(S:Finset (Fin n))(cells:Digits R.family.path.levels (Fin n))
      (q:(v:Fin n)→Choice R d v),∃X:FundedMarkedPathSelection.Input Y lo S d h A,
        X.offsets=(fun _=>parcel R same cells j) ∧
        X.familyAt=(fun y=>start R d κ pt q (places Y (fun _=>parcel R same cells j) y)) ∧
        (∀N y J,output X J N y=fixed R d κ pt N (j+1) j cells q y J) ∧
        ∀N,j<N → ∀per (y:Fin n → Cover)(J:Finset (Fin n))(a:ℕ),a≤e → ∀r,
        let printed:=output X J N y
        MarkU y J (printed.1 (R.family.side j per) a r) (printed.2 a r) ν (B^J.card):=by
  obtain ⟨A,hA,admit⟩:=WilsonCapturedPrimaryWeakTrialFixedInput.uniform (d:=d) R κ pt e
  refine ⟨A,hA,?_⟩
  filter_upwards [WilsonReceivedFixedDigitCanonical.original R d κ pt simple quiet price funded e] with j clock
  obtain ⟨ν,B,hν,hB,price⟩:=clock (j+1) (Nat.le_succ _)
  refine ⟨ν,B,hν,hB,?_⟩
  intro Y lo same scheme width S cells q
  obtain ⟨X,invoice,offset,deposited⟩:=admit j Y lo width S q (fun _=>parcel R same cells j)
  have register (N y J):output X J N y=fixed R d κ pt N (j+1) j cells q y J:=
    (deposited N J y).trans (birth R κ pt same scheme cells N j q y J)
  refine ⟨X,offset,invoice,register,?_⟩
  intro N live per y J a stage r
  rw [register]
  exact (price N live per cells q).1 y J a stage r

end YM.Integration.WilsonNeutralTwoPrintPathFixed
end

import YM.Integration.WilsonIndependentCollarMaterialStop
import YM.Integration.WilsonIndependentCollarDatedAddressed

/-! The submitted complete ordinary word at any enrolled stop continues
from its true intermediate fixed bank with the same reserve and tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarSubmittedStop
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

open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding


open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series

open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset


open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead

open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathDatedPolynomial (row sheet entry)
open WilsonReceivedCoverGrade (Same)
open FundedMarkedPathSelection (output)

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram

open WilsonOriginalCensusFaceSites (binder port pin frill root)
open WilsonOriginalCensusDatedSheets (sideValue)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonOriginalCensusFaceSheet (Addressed recenter)
open WilsonIndependentCollarAddressedSource (Submitted)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonOriginalCensusFaceIncome (addressed)
open WilsonReceivedCanonicalSocketSeed (contact present)
open WilsonOriginalCensusFaceSchools (Account)
open WilsonOriginalCensusFixedBank (Income)


open WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonIndependentCollarOrdinaryCruise (address)


variable {G:Gauge}{n:ℕ}{D k:Fin n→ℕ}{R:Run G}{N K c i:ℕ}
  (κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)(cells:Digits R.family.path.levels (Fin n))
  (seed:(v:Fin n)→Choice R k v)

theorem continued (simple:G.Simple)(vc:i≤c)(ck:c≤K)(kn:K≤N)
    (S:Finset (Fin n))(f:Pen D S→L[ℝ] ℝ)(z:Fin n → Cover):
    tuftV f (levelsO ((fixed R k κ pt N K i cells seed) z) S)=
      cruises R.family.path.levels R.metals.O N (mass k S) c i
        (tuftV f (levelsO ((fixed R k κ pt N K c cells seed)
          (address R.family.path.levels cells (c-i) i z)) S)):=by
  let L:=R.family.path.levels
  let v:=address L cells (c-i) i z
  obtain ⟨_,_,hire⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt 0 (s:=1) zero_lt_one
  have horizon (j:ℕ)(le:j≤K)(a:Fin n → Cover):tuftV f (levelsO ((fixed R k κ pt N K j cells seed) a) S)=
      cruises L R.metals.O N (mass k S) K j
        (tuftV f (levelsO ((start R k κ pt seed) (address L cells (K-j) j a)) S)):=by
    have age:j+(K-j)=K:=by omega
    simpa only [WilsonReceivedFixedDigitCanonical.fixed,age] using
      WilsonIndependentCollarOrdinaryCruise.original L R.metals.O simple R.alloy.B.ratio
        N cells (start R k κ pt seed) (hire seed).1 S f (K-j) j a (by omega)
  have route:address L cells (K-i) i z=address L cells (K-c) c v:=by
    simpa only [show c-i+(K-c)=K-i by omega,show i+(c-i)=c by omega,v] using
      WilsonIndependentCollarMaterialStop.append L cells (c-i) (K-c) i z
  rw [horizon i (vc.trans ck),cruisesMore L R.metals.O _ vc ck,horizon c ck,route]

variable {j e:ℕ}{V:Realm G (e+1) Credit.leanC}{draw:V.draws=R.family.path.levels}{rate δ σ:ℝ}

def measured {I:Type}{n':Side}{P:Passport n' (Fin n)}{B:I→Binder P (Stock.census (Fin n))}
    (H:Material R N i e k σ B)(same:H.tests=D)(S:Finset (Fin n))(f:Pen D S→L[ℝ] ℝ)(z:Fin n → Cover):Era G ℝ:=
  tuftV (Eq.mp (congrArg (fun ds:Fin n→ℕ=>Pen ds S→L[ℝ] ℝ) same.symm) f)
    (levelsO (fun J=>output H.prior J N z) S)

theorem original (simple:G.Simple)(vc:j+1≤c)(ck:c≤K)(kn:K≤N)
    (funded:Submitted R V draw D k N K j rate δ σ)
    (digits:Digits V.draws (Fin n)){I:Type}{n':Side}{P:Passport n' (Fin n)}
    (B:I→Binder P (Stock.census (Fin n)))(front:I→Fin n)(live:∀z,front z∈(B z).mode.val)
    (positive:∀z,0 < mass k (B z).mode.val)(y:Fin n → Cover)(t:Case D):
    ∃H:Material R N (j+1) e k σ B,∃axis:H.tests=D,
      H.realm=V ∧ H.amplitude=rate ∧ H.allowance=δ ∧ H.pin=front ∧ H.root=y ∘ front ∧
      (∀z,HEq (H.source z) t) ∧
      (∀l,HEq (H.frill l) (WilsonReceivedDepositedOrbitalPrint.front (J:=(B l).mode.val) (front l) y)) ∧
      (∀[Fintype I](x:Affinity.Wallet (WilsonOriginalMixedBlockRows.room (Fin n)))(s:(Stock.census (Fin n)).Mode),
        WilsonOriginalCensusDatedHeldTariff.salary H x s=(WilsonIndependentCollarLowerMass.copies B s:ℝ)*
          (‖∏v∈s.val,(x v).val‖*‖touch t s.val‖)) ∧
      (∀l,Real.exp (σ*(B l).length)*(1+∑r,(words H l).fare r) ≤ WilsonReceivedDepositedOrbitalBudget.amount H l) ∧
      ∀(S:Finset (Fin n))(f:Pen D S→L[ℝ] ℝ)(z:Fin n → Cover),
        measured H axis S f z=
          cruises R.family.path.levels R.metals.O N (mass k S) c (j+1)
            (tuftV f (levelsO ((fixed R k κ pt N K c (onLevels draw digits) seed)
              (address R.family.path.levels (onLevels draw digits) (c-(j+1)) (j+1) z)) S)):=by
  obtain ⟨H,realm,axis,gross,rent,pin,root,profile,frills,bill,book,words⟩:=
    funded digits κ pt seed I n' P B front live positive y t
  refine ⟨H,axis,realm,gross,rent,pin,root,profile,frills,bill,words,?_⟩
  subst D
  intro S f z
  change tuftV f (levelsO (fun J=>output H.prior J N z) S)=_
  have holds:(fun J=>output H.prior J N z)=(fixed R k κ pt N K (j+1) (onLevels draw digits) seed) z:=
    funext (fun J=>eq_of_heq (book z J))
  rw [holds]
  exact continued κ pt (onLevels draw digits) seed simple vc ck kn S f z

end YM.Integration.WilsonIndependentCollarSubmittedStop
end


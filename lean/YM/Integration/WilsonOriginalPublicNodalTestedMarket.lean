import YM.Integration.WilsonOriginalPublicNodalTestedProbe
import YM.Integration.WilsonOlderFreshSoftRoseMarket

/-! The actual measured three-source rows on the normalized registered fields at their original digits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalTestedMarket
open Laurent Bloch Precision Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Embroider
open WilsonCoeffUV.Blue WilsonCoeffUV.Soil XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonOlderFreshSoftFigureReading (reading)
open WilsonOlderFreshSoftRoseCourse (grade seat)
open WilsonOlderFreshSoftRoseMarket (row Probe)
open WilsonOriginalPublicNodalTestedCore (roots)
open WilsonOriginalPublicNodalTestedFunctional (deposit)
open WilsonOriginalPublicNodalTestedChronology (rank registered)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonIndependentSpoutDoseBoundary (measure into)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(W:Initialize G){e:ℕ}(D:Fin 3→ℕ)(V:Realm G (e+1) Credit.leanC)
    (s:Finset (Fin 3))[Nonempty s](N K c:ℕ)(probe:Probe D V s)
abbrev grades (s:Finset (Fin 3)):s→ℕ:=grade ∘ seat s
abbrev channels (D:Fin 3→ℕ)(s:Finset (Fin 3)):s→ℕ:=D ∘ seat s
local instance full : Nonempty (Finset.univ:Finset s):=Finset.univ_nonempty.to_subtype
abbrev Key:=∀i:s,(R.family.labels.level ((grades s) i)).Index
variable {stamps:s→ℕ}(cut:∀i,(grades s) i<stamps i)

def tested:ℝ:=probe.test (deposit (channels D s) probe.coeff probe.phase (Finset.univ:Finset s))

def base (R:Run G)(W:Initialize G)(D:Fin 3→ℕ)(V:Realm G (e+1) Credit.leanC)
    (s:Finset (Fin 3))[Nonempty s](K c:ℕ)(probe:Probe D V s)
    {stamps:s→ℕ}(cut:∀i:s,grade (seat s i)<stamps i)(b:Key R s):Era G ℝ:=
  WilsonOriginalPublicNodalTestedChronology.registered R W (fun i:s=>grade (seat s i)) b cut
    (WilsonOriginalPublicNodalTestedCore.roots V.draws probe.digit (K-c) c probe.root) (Finset.univ:Finset s)

def mark (b:Key R s):Cost:=PowerSeries.C (tested D V s probe)*(PowerSeries.X:Cost)^(rank R (grades s) b (Finset.univ:Finset s))

def programme (R:Run G)(W:Initialize G)(D:Fin 3→ℕ)(V:Realm G (e+1) Credit.leanC)
    (s:Finset (Fin 3))[Nonempty s](N K c:ℕ)(probe:Probe D V s)
    {stamps:s→ℕ}(cut:∀i:s,grade (seat s i)<stamps i)(v:ℕ)(b:Key R s):Era G ℝ:=
  affiled (clock V.draws V.paid N K v (mark R D V s probe b))
    (cruises V.draws V.paid N (rank R (fun i:s=>grade (seat s i)) b (Finset.univ:Finset s)) K v (base R W D V s K c probe cut b))

omit [Nonempty s] in
theorem port:‖tested D V s probe‖≤1:=
  (WilsonOriginalPublicNodalTestedProbe.bounded (channels D s) probe.coeff probe.phase (Finset.univ:Finset s) probe.test).trans probe.bound

theorem dated (simple:G.Simple)(pay:V.paid=R.metals.O)(v:ℕ)(vc:v≤c)(cK:c≤K)(KN:K≤N)(b:Key R s):
    let Y:=WilsonOlderFreshSoftTrialCut.source R (channels D s) (grades s) N K c V.draws V.paid
      probe.coeff probe.phase probe.digit probe.root (Finset.univ:Finset s) probe.test b
    let seen:=cruises V.draws V.paid N (mass (grades s) (Finset.univ:Finset s)) c v Y
    seen=programme R W D V s N K c probe cut v b ∧
    into V.draws V.paid N v (ground seen)=into V.draws V.paid N K (mark R D V s probe b)*
      WilsonIndependentSpoutDoseBoundary.measure V.draws V.paid N (rank R (grades s) b (Finset.univ:Finset s)) K v (base R W D V s K c probe cut b):=by
  have valid:LocalRatio V.paid:=by rw [pay]; exact R.alloy.B.ratio
  have got:=WilsonOriginalPublicNodalTestedProbe.original R W (channels D s) (grades s) b probe.coeff probe.phase cut
    V.draws V.paid simple valid N probe.digit v c K vc cK KN probe.root (Finset.univ:Finset s) probe.test
  dsimp only at got
  rw [WilsonOriginalPublicNodalTestedProbe.valuation R (channels D s) (grades s) b probe.coeff probe.phase (Finset.univ:Finset s) probe.test] at got
  exact got

theorem original (simple:G.Simple)(pay:V.paid=R.metals.O)(v w:ℕ)(vw:v≤w)(wc:w≤c)(cK:c≤K)(KN:K≤N)
    (g:ℝ)(x:∀i,(R.family.labels.level (grade i)).Coeff)(q:ℕ)(θ:ℝ)(early:Bool):
    row (R:=R) D V s N K c w v probe g x q θ early=
      if early then WilsonOlderFreshSoftCoveredRead.cost R (grades s) V.draws V.paid N w v q θ g
        (fun i=>x (seat s i)) (programme R W D V s N K c probe cut w)
      else reading R (grades s) g (fun i=>x (seat s i)) (programme R W D V s N K c probe cut v) q θ:=by
  let P:=WilsonOlderFreshSoftTrialCut.source R (channels D s) (grades s) N K c V.draws V.paid
    probe.coeff probe.phase probe.digit probe.root (Finset.univ:Finset s) probe.test
  have named (u:ℕ)(uc:u≤c):
      (fun b=>cruises V.draws V.paid N (mass (grades s) (Finset.univ:Finset s)) c u (P b))=programme R W D V s N K c probe cut u:=by
    funext b
    exact (dated R W D V s N K c probe cut simple pay u uc cK KN b).1
  cases early with
  | false=>
    change reading R (grades s) g _ (fun b=>cruises V.draws V.paid N (mass (grades s) (Finset.univ:Finset s)) c v (P b)) q θ=_
    rw [named v (vw.trans wc)]
    rfl
  | true=>
    change WilsonOlderFreshSoftCoveredRead.cost R (grades s) V.draws V.paid N w v q θ g _
      (fun b=>cruises V.draws V.paid N (mass (grades s) (Finset.univ:Finset s)) c w (P b))=_
    rw [named w wc]
    rfl

end YM.Integration.WilsonOriginalPublicNodalTestedMarket
end

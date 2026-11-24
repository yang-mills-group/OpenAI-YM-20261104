import YM.Integration.WilsonIndependentCollarDatedLowerWallet
import YM.Integration.WilsonIndependentCollarDatedTeachers
import YM.Integration.WilsonIndependentCollarOriginalWages

/-! The originally chosen bank keeps all relative lifts of each occupied
face and the ordinary winding salary of its one mounted physical test. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarAddressedSource
open Filter Function Finset Lattice RG RG.Supply Org Wilson Precision QuadraticLocal QuadraticLocal.Earn Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Legato WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Blue WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos WilsonCoeffUV.Wheel.Express
open WilsonOriginalOpticalSchedule WilsonOriginalAllOrderCalendar WilsonOriginalCollarTeacher
open WilsonOriginalCollarElection WilsonIndependentCollarCensusCourse WilsonReceivedCanonicalVerseBasis
open WilsonThermometerDeclaredSeeds WilsonReceivedFixedDigitHistory FundedMarkedPathSelection
open WilsonCoeffUV.Wheel.Cadenza WilsonOlderFreshConnectedRobe WilsonOlderFreshConnectedAppointment
open WilsonOriginalCensusDatedMaterial (words Material)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedFixedDigitCanonical (fixed)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n e:ℕ}{D k:Fin n→ℕ}

def Submitted (R:Run G)(V:Realm G (e+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (D k:Fin n→ℕ)(N K j:ℕ)(rate δ σ:ℝ):Prop:=
  ∀(cells:Digits V.draws (Fin n))(κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)(seed:(v:Fin n)→Choice R k v),
    ∀(I:Type)(n':Side)(P:Passport n' (Fin n))(B:I→Binder P (Stock.census (Fin n)))
    (c:I→Fin n), (∀z,c z∈(B z).mode.val) → (∀z,0 < mass k (B z).mode.val) →
    ∀(y:Fin n → Cover)(t:Case D),∃H:Material R N (j+1) e k σ B,
      H.realm=V ∧ H.tests=D ∧ H.amplitude=rate ∧ H.allowance=δ ∧ H.pin=c ∧ H.root=y ∘ c ∧
      (∀z,HEq (H.source z) t) ∧
      (∀l,HEq (H.frill l) (WilsonReceivedDepositedOrbitalPrint.front (J:=(B l).mode.val) (c l) y)) ∧
      (∀[Fintype I](x:Affinity.Wallet (WilsonOriginalMixedBlockRows.room (Fin n)))(s:(Stock.census (Fin n)).Mode),
        WilsonOriginalCensusDatedHeldTariff.salary H x s=(WilsonIndependentCollarLowerMass.copies B s:ℝ)*
          (‖∏v∈s.val,(x v).val‖*‖touch t s.val‖)) ∧
      (∀z J,HEq (output H.prior J N z) (fixed R k κ pt N K (j+1) (onLevels draw cells) seed z J)) ∧
      ∀l,Real.exp (σ*(B l).length)*(1+∑r,(words H l).fare r) ≤ WilsonReceivedDepositedOrbitalBudget.amount H l

theorem print (R:Run G)(V:Realm G (e+1) Credit.leanC)(D k:Fin n→ℕ)(N K j:ℕ)(hj:V.anchor ≤ j+1)
    (draw:V.draws=R.family.path.levels)(chart:V.paid=R.metals.O)
    (closed:Cloze D k V Credit.leanC)(tickets:Insure n (mass k univ) V Credit.leanC)
    {rate δ σ:ℝ}(enrolled:Paid R V hj D k δ σ)(apos:0≤rate)(width:0<σ)(top:K≤N)(up:j+2≤K)
    (earned:∀(κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)(cells:Digits V.draws (Fin n))(seed:(v:Fin n)→Choice R k v),
      Uniform V (itinerary V.draws V.paid k N cells (K-(j+2)) (j+2)
        (WilsonReceivedCanonicalVerseRegister.start R k κ pt seed)) (j+2) (by omega) rate):
    Submitted R V draw D k N K j rate δ σ:=by
  intro cells κ pt seed I n' P B c live deep y t
  let filed:=WilsonIndependentCollarDatedMaterial.filed R V B hj cells κ pt seed top up enrolled apos width
    (earned κ pt cells seed) c live deep y t closed tickets
  refine ⟨filed,rfl,rfl,rfl,rfl,rfl,rfl,fun _=>HEq.rfl,fun _=>HEq.rfl,?_,?_,?_⟩
  · intro _ x s
    exact WilsonIndependentCollarLowerMass.charge filed x s t (fun _=>rfl)
  · intro z J
    exact heq_of_eq (WilsonIndependentCollarDatedMaterial.original R V B hj cells κ pt seed top up enrolled apos width
      (earned κ pt cells seed) c live deep y t closed tickets draw chart z J)
  · intro l
    simpa only [Marker.Poly.toll,prod_const_one,one_mul] using WilsonIndependentCollarDatedMaterial.posted
      R V B hj cells κ pt seed top up enrolled apos width (earned κ pt cells seed) c live deep y t closed tickets l

end YM.Integration.WilsonIndependentCollarAddressedSource
end

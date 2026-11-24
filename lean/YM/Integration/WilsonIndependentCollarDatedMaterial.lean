import YM.Integration.WilsonIndependentCollarDatedPrior
import YM.Integration.WilsonReceivedDepositedOrbitalLedger
import YM.Integration.WilsonReceivedDepositedOrbitalBudget

/-! File the actual fixed-child chronological film in the census material
consumed by the lower probe, with its original binder and compact-word charge. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarDatedMaterial
open Finset Function Lattice RG Wilson Precision PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Cadenza QuadraticLocal Multi Marker
open WilsonReceivedFixedDigitHistory FundedMarkedPathSelection WilsonReceivedCanonicalVerseBasis
open WilsonThermometerDeclaredSeeds WilsonOlderFreshConnectedAppointment WilsonOlderFreshConnectedRobe
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonOriginalCensusDatedMaterial (Material words)
open WilsonIndependentCollarDatedPrior (inlet onLevels)
open FullQLocal Work.F08
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}{n q j N K:ℕ}{D k:Fin n→ℕ}{n':Side}
  {P:Earn.Passport n' (Fin n)}(R:Run G)(V:Realm G (q+1) Credit.leanC)
  (B:I→Earn.Binder P (Stock.census (Fin n)))(hj:V.anchor ≤ j+1)
  (cells:Digits V.draws (Fin n))(κ:(l:Fin n)→Knob (D l))(pt:Fin n→Chamber)(seed:(l:Fin n)→Choice R k l)
  (top:K≤N)(up:j+2≤K){A δ σ:ℝ}(paid:Paid R V hj D k δ σ)(apos:0≤A)(width:0<σ)
  (wallet:Uniform V (itinerary V.draws V.paid k N cells (K-(j+2)) (j+2) (start R k κ pt seed))
    (j+2) (by omega) A)(c:I→Fin n)(pin:∀l,c l∈(B l).mode.val)(deep:∀l,0 < mass k (B l).mode.val)
  (y:Fin n → Cover)(t:Case D)(closed:Cloze D k V Credit.leanC)(tickets:Insure n (mass k univ) V Credit.leanC)

local notation "X" => inlet R V (j+1) hj univ N K top up cells κ pt seed A wallet

def filed:Material R N (j+1) q k σ B:=
  WilsonReceivedDepositedOrbitalLedger.book R V hj paid N (X) apos (by omega) width B c
    (fun _=>subset_univ _) pin deep y t closed tickets

local notation "H" => filed R V B hj cells κ pt seed top up paid apos width wallet c pin deep y t closed tickets

theorem original (draw:V.draws=R.family.path.levels)(chart:V.paid=R.metals.O)(z:Fin n → Cover)(J:Finset (Fin n)):
    output (H).prior J N z=fixed R k κ pt N K (j+1) (onLevels draw cells) seed z J:=
  WilsonIndependentCollarDatedPrior.original R V (j+1) hj univ N K top up cells κ pt seed A wallet draw chart z J

theorem posted (l:I):
    Real.exp (σ*(B l).length)*(1+∑a,(words (H) l).fare a) ≤
      Poly.toll (fun _:Fin n=>(1:ℝ)) (B l).mode*WilsonReceivedDepositedOrbitalBudget.amount (H) l:=
  WilsonReceivedDepositedOrbitalBudget.posted (H) l

end YM.Integration.WilsonIndependentCollarDatedMaterial
end

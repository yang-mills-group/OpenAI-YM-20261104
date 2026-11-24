import YM.Integration.WilsonIndependentCollarDatedAddressed
import YM.Integration.WilsonIndependentCollarDatedPublication
import YM.Integration.WilsonIndependentCollarMaterialCost
import YM.Integration.WilsonIndependentCollarOrbitalDose
import YM.Integration.WilsonIndependentCollarOrbitalReception

/-! The fixed-K material of the paid Wilson election keeps its full rooted
countable source and the exact paint and signed wallet of each physical
binder. The angular operator is charged once per occupied block. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarDatedProbeSalary
open Filter Function Finset Lattice RG RG.Supply Org Wilson Precision QuadraticLocal QuadraticLocal.Earn Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Legato WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Blue WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Wheel.Address Marker Multi
open WilsonCoeffUV.Mer.Rolls (feeH)
open WilsonOriginalOpticalSchedule WilsonOriginalAllOrderCalendar WilsonOriginalCollarTeacher
open WilsonOriginalCollarElection WilsonIndependentCollarCensusCourse WilsonReceivedCanonicalVerseBasis
open WilsonThermometerDeclaredSeeds WilsonReceivedFixedDigitHistory FundedMarkedPathSelection
open WilsonCoeffUV.Wheel.Cadenza WilsonOlderFreshConnectedRobe WilsonOlderFreshConnectedAppointment
open WilsonOriginalCensusDatedMaterial (words Material)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonIndependentCollarAddressedSource (Submitted)
open WilsonIndependentCollarOrbitalPeg (ink)
open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonOriginalMixedBlockRows (room)
open scoped Classical BigOperators Topology

variable {G:Gauge}{n q:ℕ}{R:Run G}{V:Realm G (q+1) Credit.leanC}{draw:V.draws=R.family.path.levels}
 {I:Type}[Fintype I][DecidableEq I]{side:Side}{P:Passport side (Fin n)}{B:I→Binder P (Stock.census (Fin n))}
 {D k:Fin n→ℕ}{N K j:ℕ}{σ rate δ:ℝ}

private theorem source_paid (H:Material R N (j+1) q k σ B)(t:Case D)(same:H.tests=D)(chosen:∀z,HEq (H.source z) t)
    (amplitude:H.amplitude=rate)(allowance:H.allowance=δ) :
    (∀(x:Affinity.Wallet (room (Fin n)))(target:(Stock.census (Fin n)).Mode),
      (∑s:Finset I,‖wages B x target s‖ * ∏z∈s,‖ink (H.source z) (B z).mode.val‖) ≤
        (2:ℝ)^(Fintype.card I) * ∏v∈target.val,‖(x v).val‖*‖t v‖) ∧
    (∀z,WilsonIndependentCollarMaterialIntensity.price H z≤
      ((q+1:ℕ):ℝ)*((mass k (B z).mode.val+q+1:ℕ):ℝ)*
        ((∏v∈(B z).mode.val,‖t v‖)*|(R.family.path.levels.clock.hatBeta (j+1))^δ*rate^(B z).mode.val.card|)) := by
  subst D
  have paint : ∀z,H.source z=t:=fun z=>eq_of_heq (chosen z)
  constructor
  · intro x target
    simp only [paint]
    exact WilsonIndependentCollarOrbitalDose.original B x t target
  · intro z
    have pay:=WilsonIndependentCollarMaterialCost.original H z
    rw [paint z,amplitude,allowance] at pay
    exact pay

/-- The selected original appointment supplies this particular predecessor, at
all periods and every upper cutoff of its paid window. -/
theorem original (issued:Submitted R V draw D k N K j rate δ σ)
    (cells:Digits V.draws (Fin n))(κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)(seed:(v:Fin n)→Choice R k v)
    (c:I→Fin n)(live:∀z,c z∈(B z).mode.val)(deep:∀z,0 < mass k (B z).mode.val)(y:Fin n → Cover)(t:Case D):
    ∃H:Material R N (j+1) q k σ B,
      H.realm=V ∧ H.tests=D ∧ H.pin=c ∧ H.root=y ∘ c ∧ (∀z,HEq (H.source z) t) ∧
      (∀l,HEq (H.frill l) (WilsonReceivedDepositedOrbitalPrint.front (J:=(B l).mode.val) (c l) y)) ∧
      (∀z J,HEq (output H.prior J N z) (fixed R k κ pt N K (j+1) (onLevels draw cells) seed z J)) ∧
      (∀z,WilsonOriginalPrimerStampedRay.Matched (words H z) (WilsonOriginalCensusDatedMaterial.charts H z)) ∧
      (∀z,Real.exp (σ*(B z).length)*WilsonIndependentCollarSlateIntensity.amount (words H z) (B z).center ≤
         Real.exp (σ*(B z).length-32*σ*(feeH (toe (B z).mode.val (H.pin z) (H.root z) (H.frill z))
           (H.pin z) (B z).mode.val))*WilsonIndependentCollarMaterialIntensity.price H z) ∧
      (∀(x:Affinity.Wallet (room (Fin n)))(target:(Stock.census (Fin n)).Mode),
        (∑s:Finset I,‖wages B x target s‖ * ∏z∈s,‖ink (H.source z) (B z).mode.val‖) ≤
          (2:ℝ)^(Fintype.card I) * ∏v∈target.val,‖(x v).val‖*‖t v‖) ∧
      (∀z,WilsonIndependentCollarMaterialIntensity.price H z≤
        ((q+1:ℕ):ℝ)*((mass k (B z).mode.val+q+1:ℕ):ℝ)*
          ((∏v∈(B z).mode.val,‖t v‖)*|(R.family.path.levels.clock.hatBeta (j+1))^δ*rate^(B z).mode.val.card|)) := by
  obtain ⟨H,realm,tests,amplitude,allowance,front,root,paint,frill,_,prior,_⟩:=
    issued cells κ pt seed I side P B c live deep y t
  have bought:=source_paid H t tests paint amplitude allowance
  exact ⟨H,realm,tests,front,root,paint,frill,prior,WilsonOriginalCensusDatedMaterial.matched H,
    WilsonIndependentCollarMaterialWallet.original H,bought⟩

end YM.Integration.WilsonIndependentCollarDatedProbeSalary
end

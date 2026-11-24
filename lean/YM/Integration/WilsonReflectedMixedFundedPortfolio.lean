import YM.Integration.WilsonReflectedMixedFiniteConditional
import YM.Integration.WilsonReflectedMixedPortfolio
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedFundedPortfolio
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records MergeProof Push.Local Motion
open WilsonReflectedFundedHearing WilsonReflectedOpticalArm WilsonMeasuredPublicEntranceGridDebit
open WilsonAddressedMixedEnrolledTrial WilsonOriginalMicroscopicGuardedReporters
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I]
local notation "C" => R.family
local notation "H" => (C).path.levels.clock.hatBeta


open WilsonReflectedMixedThermalArms

open Filter Trace.Physical.GermGraph
open scoped Topology



open WilsonReflectedOriginalTwoDeposit (raw held)
open WilsonReflectedFundedHearing (Arm source cropped signed)
open WilsonReflectedMixedSharpAxis (Cash)

theorem mounted {d j f K N p order:ℕ}{before:j≤f}{up:f≤K}{live:K≤N}{η wage:ℝ}
    {B:(C).label d≃ₗ[ℂ](C).label d}{Y:(C).label d}(paid:WilsonReflectedMixedSharpAxis.Cash (R:=R) d j f K N p order before up live η B Y wage)
    (b:Bool)(s:Signed)(o:Site ((C).side f p)):
    ∃A:Arm R d N p f K,A.Y=Y ∧ A.w=B.symm (fitted R d j N p Y) ∧ A.b=b ∧ A.s=s ∧ A.o=o ∧
      A.cash=WilsonMeasuredPublicEntranceGridDebit.bill R d K f A.w:=by
  obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le up
  have pay:=paid.2.2.1 (0:Site ((C).side f p))
  simp only [Nat.add_sub_cancel_left] at pay
  obtain ⟨z,registration,_⟩:=pay
  exact ⟨⟨Y,_,b,s,o,_,z,registration⟩,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem emitted {ι:Type}[Fintype ι]{d f K N p:ℕ}(top:f≤N)
    (A:Arm R d N p f K)(rows:ι→Arm R d N p f K)(c:ι→ℂ)
    (sites:∀i,(rows i).o=A.o)(moves:∀i,((rows i).s,(rows i).b)=(A.s,A.b))
    (born:A.Y=∑i,c i•(rows i).Y)(U:Config G ((C).side N p)):
    raw R (source R A top) U=∑i,Motion.scalar (A.s,A.b) (c i)*raw R (source R (rows i) top) U:=by
  have turns i:(rows i).s=A.s:=congrArg Prod.fst (moves i)
  have hands i:(rows i).b=A.b:=congrArg Prod.snd (moves i)
  cases bit:A.b <;>
    simp [WilsonReflectedOriginalTwoDeposit.raw,WilsonReflectedFundedHearing.source,WilsonReflectedPlacedArm.original,Push.RelayDifference.oriented,Push.RelayDifference.hand,sites,
      turns,hands,bit,born,WilsonReflectedMixedCutoffField.physical,Motion.scalar]

/-- The signed density includes every forced component of the selected true
reporter account, evaluated at its own turned original site. -/
theorem original {ι:Type}[Fintype ι]{d f K N p:ℕ}(up:f≤K)(live:K≤N)(ready:(C).ref d≤f)
    (A:Arm R d N p f K)(rows:ι→Arm R d N p f K)(c:ι→ℂ)
    (sites:∀i,(rows i).o=A.o)(moves:∀i,((rows i).s,(rows i).b)=(A.s,A.b))
    (born:A.Y=∑i,c i•(rows i).Y)(entered:A.w=∑i,c i•(rows i).w)(W:Config G ((C).side f p)):
    signed R A W=∑i,Motion.scalar (A.s,A.b) (c i)*signed R (rows i) W:=by
  let χ:=fun i=>Motion.scalar (A.s,A.b) (c i)
  let fin:=up.trans live
  let cutoff:=fun i=>raw R (source R (rows i) fin)
  have fresh:held R (source R A fin) f W=∑i,χ i*held R (source R (rows i) fin) f W:=by
    simp only [WilsonReflectedOriginalTwoDeposit.held,dif_pos fin]
    have same:=funext (emitted R fin A rows c sites moves born)
    rw [same]
    exact WilsonReflectedMixedFiniteConditional.weighted R le_rfl fin cutoff
      (fun i=>Envelope.compactC (WilsonReflectedOriginalTwoDeposit.continuous R _)) χ W
  let masked:=fun i=>cropped R (rows i) up
  have fitted:WilsonReflectedRestartedPair.mean R N (cropped R A up) f W=
      ∑i,χ i*WilsonReflectedRestartedPair.mean R N (masked i) f W:=by
    simp only [WilsonReflectedRestartedPair.mean,dif_pos up]
    have same:=funext (WilsonReflectedMixedTrialField.field R up A rows c sites moves entered)
    rw [same]
    exact WilsonReflectedMixedFiniteConditional.weighted R live up masked
      (fun i=>WilsonReflectedPlacedArm.trial_paid R ..) χ W
  rw [←WilsonReflectedFundedHearing.swap R A up live ready W,fresh,fitted,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←mul_sub]
  exact congrArg (χ i * ·) (WilsonReflectedFundedHearing.swap R (rows i) up live ready W)

end YM.Integration.WilsonReflectedMixedFundedPortfolio
end

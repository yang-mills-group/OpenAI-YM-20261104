import YM.Integration.WilsonReflectedOpticalArm
import YM.Integration.WilsonReflectedEmbeddedLocations
/-! Retain the native same-cutoff residual at the embedded K site of an
actually purchased reporter arm. It has the same original microscopic
numerator and the same guarded trial on all K fields. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedRestoredStation
open Push Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn WilsonReflectedOriginalTwoDeposit
open WilsonReflectedPlacedArm WilsonReflectedFullPanel WilsonOriginalMicroscopicGuardedPage WilsonReflectedFundedHearing
open private composed same from YM.Integration.WilsonAddressedWeakTiling
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N p f K d:ℕ}
local notation "C₀" => R.family

def Situated (front:f≤K)(A:Arm R d N p f K)(B:Arm R d N p K K):Prop:=
  B.Y=A.Y ∧ B.w=A.w ∧ B.b=A.b ∧ B.s=A.s ∧ B.o=((C₀).S.toDepth front p).embed A.o

theorem purchased {j q:ℕ}(front:f≤K)(start:j≤K)(high:K≤N){η bank:ℝ}
    {M:(C₀).label d ≃ₗ[ℂ] (C₀).label d}(A:Arm R d N p f K)
    (receipt:WilsonReflectedFullPanel.receipt R d j K N p q start high η M A.Y bank)
    (sameValue:A.w=M.symm (full R d N p j A.Y)):
    ∃B:Arm R d N p K K,Situated R front A B ∧
      B.cash=hike (C₀) K K rate*((1+4*stock (C₀) K)*((C₀).labels.level d).coeffSize A.w):=by
  obtain ⟨B,by₀,bw,bb,bs,bo,fee⟩:=WilsonReflectedFundedHearing.purchased R d j q start high start le_rfl receipt A.b A.s (((C₀).S.toDepth front p).embed A.o)
  exact ⟨B,⟨by₀,bw.trans sameValue.symm,bb,bs,bo⟩,by rw [fee,bw,sameValue]⟩

theorem traded (front:f≤K)(high:K≤N)(A:Arm R d N p f K)(B:Arm R d N p K K)
    (found:Situated R front A B):
    source R B high=source R A (front.trans high) ∧ cropped R B le_rfl=cropped R A front:=by
  obtain ⟨ay,aw,ab,as',ao⟩:=found
  constructor
  · unfold source WilsonReflectedPlacedArm.original;rw [ay,ab,as',ao,composed ((C₀).S.toDepth front p)
      ((C₀).S.toDepth high p) ((C₀).S.toDepth (front.trans high) p)]
  · unfold cropped WilsonReflectedPlacedArm.trial;rw [aw,ab,as',ao,same]

theorem original (front:f≤K)(high:K≤N)(active:(C₀).ref d≤K)(A:Arm R d N p f K)(B:Arm R d N p K K)
    (found:Situated R front A B)(U:Config G ((C₀).side K p)):
    held R (source R A (front.trans high)) K U-cropped R A front U=signed R B U:=by
  obtain ⟨direct,trial⟩:=traded R front high A B found
  have native:=WilsonReflectedFundedHearing.swap R B le_rfl high active U
  rw [WilsonReflectedRestartedPair.mean,dif_pos le_rfl,actualTransport_base (C₀) R.makes high,direct,trial] at native
  exact native

end YM.Integration.WilsonReflectedRestoredStation
end

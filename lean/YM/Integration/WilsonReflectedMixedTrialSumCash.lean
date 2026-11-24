import YM.Integration.WilsonReflectedMixedTrialMap
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedTrialSumCash
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



open WilsonReflectedMixedSharpAxis (Cash)

theorem normed {ι:Type}[Fintype ι]{d:ℕ}(c:ι→ℂ)(w:ι→(C).label d):
    ((C).labels.level d).coeffSize (∑i,c i•w i)≤∑i,‖c i‖*((C).labels.level d).coeffSize (w i):=by
  classical
  unfold Frame.coeffSize
  simp only [Finset.sum_apply,Pi.smul_apply,Finset.mul_sum]
  exact (Finset.sum_le_sum (fun b _=> (norm_sum_le _ _).trans
    (Finset.sum_le_sum (fun i _=>le_of_eq (norm_smul (c i) (w i b)))))).trans_eq Finset.sum_comm

/-- Fixed complex combinations of any already purchased original K columns
are paid on their true sharp stretch and the same once-scaled guard. -/
theorem original {ι:Type}[Fintype ι]{d j f K N p current order:ℕ}{first:j≤f}{up:f≤K}{top:K≤N}
    (admit:Opened C d j p){η η':ℝ}{F A:(C).label d≃ₗ[ℂ](C).label d}
    (master:∀x,Arrived R d j K N p current (first.trans up) top η F x)
    (c:ι→ℂ)(Y:ι→(C).label d)(B:ι→(C).label d≃ₗ[ℂ](C).label d)(W:ι→ℝ){orders:ι→ℕ}
    (bought:∀i,Cash (R:=R) d j f K N p (orders i) first up top η (B i) (Y i) (W i))
    (total:Arrived R d j K N p order (first.trans up) top η' A (fitted R d j N p (∑i,c i•Y i))):
    let w:=A.symm (fitted R d j N p (∑i,c i•Y i))
    let income:=∑i,‖c i‖*W i
    ((C).labels.level d).coeffSize w≤ stretch R η j K*(2*((C).S.a j^d*income)) ∧
    ∀χ:ℝ,0<χ→((C).labels.level d).coeffSize (WilsonAddressedPublicGuardFare.word R d K χ w) ≤
      4*(income/χ)*((C).S.a j/(C).S.a K)^((d:ℝ)+η):=by
  intro w income
  have decomp:w=∑i,c i•(B i).symm (fitted R d j N p (Y i)):=
    WilsonReflectedMixedTrialMap.original R admit master c Y B (fun i=>(bought i).1 _) total
  have bound:((C).labels.level d).coeffSize w ≤ stretch R η j K*(2*((C).S.a j^d*income)):=by
    rw [decomp]
    apply (normed R c _).trans
    apply (Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (bought i).2.1 (norm_nonneg (c i)))).trans_eq
    dsimp only [income]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact ⟨bound,fun χ pos=>WilsonAddressedPublicGuardFare.cost R pos bound⟩

end YM.Integration.WilsonReflectedMixedTrialSumCash
end

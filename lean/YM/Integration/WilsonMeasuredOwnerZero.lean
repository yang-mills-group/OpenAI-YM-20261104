import YM.Integration.WilsonMeasuredOnlyHard
import YM.Integration.WilsonMeasuredOwnerKernel

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerZero
open Lattice Wilson RG Labels Source Extra.Histories Trace.Physical Trace.Physical.GermGraph
open WilsonMeasuredCoefficientTransport PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge} {d:ℕ} {F:Frame G d} {n:Side}

/-- A zero native invoice kills the entire forced numerator with its actual
admissible owner lists and all their partners. -/
theorem field {o:Site n} {P:Rep G n} {h:Coefficient F n} {κ:ℝ}
    (paid:h.remBound o P κ 0) : account h P=0:=by
  obtain ⟨a,b,an,bn,limit,_,_,e,invoice,cap⟩:=paid
  have b0 : b=0:=by linarith
  have gone (i:ℕ) (U:Config G n): h.forced i U=0:=by
    have zero:= (invoice.2.1.le_tsum i (fun j _=>invoice.1 j)).trans invoice.2.2
    rw [b0,mul_zero] at zero
    have fee:e i ≤ 0:=by
      by_contra! positive
      exact (not_lt_of_ge zero) (mul_pos (Real.exp_pos _) positive)
    exact norm_le_zero_iff.mp (((cap i).2 U).trans fee)
  funext U
  have all (b:Finset ℕ):h.marked P b U=0:=by
    unfold Coefficient.marked
    split
    · simp only [gone,zero_mul,Finset.sum_const_zero]
    · rfl
  simp [account,all]

theorem transported (R:Run G) {i N per:ℕ}
    {P:Rep G (R.family.side (i+1) per)} {h:Coefficient (R.family.labels.level d) (R.family.side (i+1) per)}
    {κ:ℝ} (paid:h.remBound 0 P κ 0) :
    GermGraph.transition (C:=R.family) d N per i (account h P)=0:=by
  rw [field paid]
  funext U
  simp [GermGraph.transition,blast,RG.StepData.push]

end YM.Integration.WilsonMeasuredOwnerZero

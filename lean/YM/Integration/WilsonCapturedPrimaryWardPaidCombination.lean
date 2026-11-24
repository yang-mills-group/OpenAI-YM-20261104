import YM.Integration.WilsonCapturedPrimaryWardPaidSource
import YM.Integration.IntrinsicProductLinearity

/-! Common fixed-date fields under finite signed combinations of genuine booked sources. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section

namespace YM.Integration.WilsonCapturedPrimaryWardPaidCombination
open Function Set Filter MeasureTheory Finset Lattice Wilson RG Source Labels OPE OPE.Cards RG12
open RG16 RG16.Literal Trace.Physical.GermGraph Cells MergeProof PhysicalNext.Repeat.Legato
open Extra.Histories
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) {N p d j u:ℕ}
variable {ι:Type} [Fintype ι] [Nonempty ι]
variable (door:Opened R.family d u p) (un:u ≤ N) (live:j ≤ N)

local notation "Z" => Cut R.family N p
local notation "C!" => WilsonMacroscopicRichChildRegistration.returned R.family R.makes door un

include live in
theorem original (w:ι→ℂ) (Y:ι→Z) (fee:ι→ℝ) (cont:∀i,Continuous (Y i))
    (panel:∀i,Booked R.family N p d (Y i) u un ∧ PaidAt R.family.S N p j (R.family.beta N p)
      (fee i) (Y i-R.family.O N p (C! (Y i)) 0)) :
    let Q:=∑i,w i • Y i
    Booked R.family N p d Q u un ∧ C! Q=∑i,w i • C! (Y i) ∧
    PaidAt R.family.S N p j (R.family.beta N p) (∑i,‖w i‖*fee i) (Q-R.family.O N p (C! Q) 0):=by
  intro Q
  have entry:=IntrinsicProductLinearity.booked_sum R.family N p d u R.makes door un w Y cont (fun i=>(panel i).1)
  have filed:C! Q=∑i,w i • C! (Y i):=by
    unfold WilsonMacroscopicRichChildRegistration.returned
    rw [entry.2,map_sum]
    exact Finset.sum_congr rfl (fun i _=>map_smul _ _ _)
  let L:R.family.label d→ₗ[ℂ] Z:=(R.family.linearO N p d 0).mk' _
  let f (i:ι) : Z := Y i-L (C! (Y i))
  have residual:Q-R.family.O N p (C! Q) 0=∑i,w i • f i:=by
    change Q-L (C! Q)=_
    rw [filed,map_sum]
    simp only [Q,f,map_smul,smul_sub,Finset.sum_sub_distrib]
  have roots:=Next.UVStress.root_sum (center R.family.S p live 0) (R.family.beta N p) univ f w
    (fun i _=>(panel i).2.ticket) (seamless R.makes N p)
  refine ⟨entry.1,filed,?_⟩
  rw [residual]
  exact ⟨live,roots.1,roots.2.trans (sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (panel i).2.mark (norm_nonneg _))⟩

end YM.Integration.WilsonCapturedPrimaryWardPaidCombination

import YM.Integration.WilsonCapturedPrimaryWardPaidRate

/-! Sparse fixed-date linearity on any horizon, including the identically zero physical test. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section

namespace YM.Integration.WilsonCapturedPrimaryWardPaidSparse
open Function Set Filter MeasureTheory Finset Lattice Wilson RG Source Labels OPE OPE.Cards RG12
open RG16 RG16.Literal Trace.Physical.GermGraph Cells MergeProof PhysicalNext.Repeat.Legato
open Bid Extra.Histories
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) {N p d j u:ℕ}
variable (door:Opened R.family d u p) (un:u ≤ N) (live:j ≤ N)

local notation "Z" => Cut R.family N p
local notation "C!" => WilsonMacroscopicRichChildRegistration.returned R.family R.makes door un

include live in
theorem empty : Booked R.family N p d (0:Z) u un ∧ C! (0:Z)=0 ∧
    PaidAt R.family.S N p j (R.family.beta N p) 0 ((0:Z)-R.family.O N p (C! (0:Z)) 0):=by
  let F:=R.family.labels.level d
  let q:store R.family d p u:=primary 0 (0:F.Coeff)
  have booked:Booked R.family N p d (0:Z) u un:=by
    refine ⟨q,0,⟨primary_format ..,primary_rem _ (Real.sqrt_pos.mpr (forcedPos _ _))⟩,?_⟩
    have zero:=IntrinsicProductLinearity.credit_sum R.family N p d u un (fun _:Unit=>(0:ℂ))
      (fun _:Unit=>(0:Z)) (fun _=>continuous_const)
    have quiet:credit R.family N p d (0:Z) u un=0:=by simpa using zero
    rw [quiet]
    funext V
    simp [q,value,primary_density]
  have ret:=IntrinsicProductLinearity.booked_sum R.family N p d u R.makes door un (fun _:Unit=>(0:ℂ))
    (fun _:Unit=>(0:Z)) (fun _=>continuous_const) (fun _=>booked)
  have hat:topReport R.family N p d R.makes u door un (0:Z)=0:=by simpa using ret.2
  have null:C! (0:Z)=0:=by simp [WilsonMacroscopicRichChildRegistration.returned,hat]
  let L:R.family.label d→ₗ[ℂ] Z:=(R.family.linearO N p d 0).mk' _
  have row:R.family.O N p (0:R.family.label d) 0=(0:Z):=map_zero L
  rw [null,row,sub_zero]
  refine ⟨booked,rfl,live,Interior.constant ..,?_⟩
  rw [show (0:Z)=(0:ℂ) • (1:Z) from (zero_smul ..).symm,Next.UVStress.root_smul,norm_zero,zero_mul]

variable {ι:Type} [Fintype ι] [Nonempty ι]
include live in
theorem original (w:ι→ℂ) (Y:ι→Z) (fee:ι→ℝ) (cont:∀i,Continuous (Y i))
    (panel:∀i,w i≠0 → Booked R.family N p d (Y i) u un ∧
      PaidAt R.family.S N p j (R.family.beta N p) (fee i) (Y i-R.family.O N p (C! (Y i)) 0)) :
    let Q:=∑i,w i • Y i
    Booked R.family N p d Q u un ∧ C! Q=∑i,w i • C! (Y i) ∧
    PaidAt R.family.S N p j (R.family.beta N p) (∑i,‖w i‖*fee i) (Q-R.family.O N p (C! Q) 0):=by
  intro Q
  let Y₀(i:ι):Z:=if w i=0 then 0 else Y i
  let cap(i:ι):ℝ:=if w i=0 then 0 else fee i
  have owns(i:ι):Booked R.family N p d (Y₀ i) u un ∧ PaidAt R.family.S N p j (R.family.beta N p)
      (cap i) (Y₀ i-R.family.O N p (C! (Y₀ i)) 0):=by
    by_cases hz:w i=0
    · have result:=empty (N:=N) (p:=p) R door un live
      simpa [Y₀,cap,hz] using And.intro result.1 result.2.2
    · simpa [Y₀,cap,hz] using panel i hz
  have smooth(i:ι):Continuous (Y₀ i):=by
    by_cases hx:w i=0
    · dsimp only [Y₀]
      rw [if_pos hx]
      change Continuous (fun _:Config G (R.family.side N p)=>(0:ℂ))
      exact continuous_const
    · simpa only [Y₀,if_neg hx] using cont i
  have same:(∑i,w i • Y₀ i)=Q:=by
    apply sum_congr rfl
    intro i _
    by_cases hz:w i=0 <;> simp [Y₀,hz]
  have labels:(∑i,w i • C! (Y₀ i))=∑i,w i • C! (Y i):=by
    apply sum_congr rfl
    intro i _
    by_cases hz:w i=0 <;> simp [Y₀,hz]
  have budget:(∑i,‖w i‖*cap i)=∑i,‖w i‖*fee i:=by
    apply sum_congr rfl
    intro i _
    by_cases hz:w i=0 <;> simp [cap,hz]
  have paid:=WilsonCapturedPrimaryWardPaidCombination.original R door un live w Y₀ cap smooth owns
  simpa only [same,labels,budget] using paid

end YM.Integration.WilsonCapturedPrimaryWardPaidSparse

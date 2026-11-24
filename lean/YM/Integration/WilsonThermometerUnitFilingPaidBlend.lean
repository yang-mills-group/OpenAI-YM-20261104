import YM.Integration.WilsonThermometerUnitFilingBlend

/-! A finite linear combination of original reflected scalar filings. A slot
with zero weight needs no witness. The true credit books the combined source
and the common tiling hears its complete signed residual. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPaidBlend
open Function Set Filter MeasureTheory Finset Lattice Wilson RG Source Labels OPE OPE.Cards RG12
open Bid RG16 RG16.Literal Trace.Physical.GermGraph Cells MergeProof MergeProof.Accent
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFeed Next.UVStress Extra.Histories
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) {N p b u j:ℕ}

open WilsonThermometerUnitFilingBlend

variable {ι:Type} [Fintype ι] [Nonempty ι] (W:ι→ℂ) (Y:ι→Cut R.family N p)
local notation "big!" => ∑a,W a • Y a

include simple in
theorem original (ju:j≤u) (ub:u≤b) (bN:b≤N) (door:Opened R.family 0 u p)
    (smooth:∀a,Continuous (Y a)) (price:ι→ℝ)
    (returns:∀a,W a≠0 → Booked R.family N p 0 (Y a) u (ub.trans bN) ∧
      PaidAt R.family.S N p j (R.family.beta N p) (price a)
        (Y a-report R (Y a) u • (1:Cut R.family N p))):
    Booked R.family N p 0 (big!) u (ub.trans bN) ∧
    PaidAt R.family.S N p j (R.family.beta N p) (∑a,‖W a‖*price a)
      ((big!)-report R (big!) u • (1:Cut R.family N p)) :=by
  let live:=ub.trans bN
  let T:=center R.family.S p (ju.trans live) 0
  let Y0 (a:ι):Cut R.family N p:=if W a≠0 then Y a else 0
  let cost (a:ι):ℝ:=if W a≠0 then price a else 0
  have cont (a):Continuous (Y0 a):=by
    by_cases act:W a≠0
    · simp only [Y0,if_pos act];exact smooth a
    · simp only [Y0,if_neg act];exact continuous_const
  have same a:W a • Y0 a=W a • Y a:=by by_cases act:W a≠0 <;> simp_all [Y0]
  have eq: (big!)=∑a,W a • Y0 a:=Finset.sum_congr rfl fun a _=>(same a).symm
  have unit (a):Booked R.family N p 0 (Y0 a) u live ∧
      PaidAt R.family.S N p j (R.family.beta N p) (cost a)
        (Y0 a-report R (Y0 a) u • (1:Cut R.family N p)):=by
    by_cases act:W a≠0
    · simpa only [Y0,cost,if_pos act] using returns a act
    · simp only [Y0,cost,if_neg act]
      have h0:=null_booked R (p:=p) live
      have nil:credit R.family N p 0 (0:Cut R.family N p) u live=0:=by
        simpa using IntrinsicProductLinearity.credit_sum R.family N p 0 u live (fun _:Unit=>(0:ℂ))
          (fun _:Unit=>(0:Cut R.family N p)) (fun _=>continuous_const)
      have read0:=WilsonThermometerUnitFilingCourse.filed R simple (0:Cut R.family N p) door live h0
      rw [nil] at read0;simp only [Pi.zero_apply,mul_zero] at read0
      rw [read0,zero_smul,sub_zero]
      refine ⟨h0,ju.trans live,Interior.constant ..,?_⟩
      rw [show (0:Cut R.family N p)=(0:ℂ) • (1:Cut R.family N p) from (zero_smul ..).symm,
        Next.UVStress.root_smul T _ _ _,norm_zero,zero_mul]
  have entry:=IntrinsicProductLinearity.booked_sum R.family N p 0 u R.makes door live W Y0 cont (fun a=>(unit a).1)
  have fitted (Z:Cut R.family N p):report R Z u=(topReport R.family N p 0 R.makes u door live Z) 0:=by
    simp only [report,dif_pos (And.intro door live),terminal R simple (door.post.trans live)]
  have line:report R (big!) u=∑a,W a*report R (Y0 a) u:=by
    rw [eq,fitted,entry.2];simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using
      Finset.sum_congr rfl (fun a (_:a∈Finset.univ)=>congrArg (fun x:ℂ=>W a*x) (fitted (Y0 a)).symm)
  let f:=fun a=>Y0 a-report R (Y0 a) u • (1:Cut R.family N p)
  have combined:(big!)-report R (big!) u • (1:Cut R.family N p)=∑a,W a • f a:=by
    rw [line,eq];simp only [f,smul_sub,Finset.sum_sub_distrib,Finset.sum_smul,smul_smul]
  have roots:=Next.UVStress.root_sum T (R.family.beta N p) univ f W (fun a _=>(unit a).2.ticket) (seamless R.makes N p)
  refine ⟨eq ▸ entry.1,?_⟩
  rw [combined]
  refine ⟨ju.trans live,roots.1,roots.2.trans (Finset.sum_le_sum fun a _=>?_)⟩
  by_cases act:W a≠0
  · exact mul_le_mul_of_nonneg_left (by simpa [cost,act] using (unit a).2.mark) (norm_nonneg _)
  · have wa:W a=0:=not_ne_iff.mp act;simp [wa]

end YM.Integration.WilsonThermometerUnitFilingPaidBlend

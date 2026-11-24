import YM.Integration.WilsonReportingPrescribedOldConnected

/-! The actual physical submoments that enter the stability of the full normalized marked logarithm.  A whole shard is changed once, with its original companion submoments. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorPartitions
open Function Finset Marker Multi Extra.Trajectories Comparison.RG02.Cumulants
open scoped Classical BigOperators

def others {I:Type*}[DecidableEq I](s:Finset I)(B:I→ℝ):ℝ:=∑i∈s,∏j∈s.erase i,B j

private theorem inserted {I:Type*}[DecidableEq I](s:Finset I)(B:I→ℝ){i:I}(fresh:i∉s):
    others (insert i s) B=(∏j∈s,B j)+B i*others s B:=by
  unfold others
  rw [sum_insert fresh,erase_insert fresh,Finset.mul_sum]
  congr 1
  apply sum_congr rfl
  intro j hj
  have distinct:j≠i:=fun h=>fresh (h ▸ hj)
  rw [erase_insert_of_ne distinct.symm,prod_insert (fun a=>fresh (mem_of_mem_erase a))]

private theorem telescope {I:Type*}[DecidableEq I](s:Finset I)(x y:I→ℂ)(B:I→ℝ){δ:ℝ}
    (non:0≤δ)(xp:∀i,‖x i‖≤B i)(yp:∀i,‖y i‖≤B i)(fee:∀i,‖x i-y i‖≤δ):
    ‖(∏i∈s,x i)-(∏i∈s,y i)‖≤δ*others s B:=by
  induction s using Finset.induction_on with
  | empty => simp [others]
  | @insert i s fresh prior =>
    rw [prod_insert fresh,prod_insert fresh,inserted s B fresh]
    let X:=∏j∈s,x j
    let Y:=∏j∈s,y j
    have bx:‖X‖≤∏j∈s,B j:=by
      change ‖∏j∈s,x j‖≤_
      rw [norm_prod]
      exact prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>xp j)
    have bi:0≤B i:=(norm_nonneg _).trans (yp i)
    calc
      _=‖(x i-y i)*X+y i*(X-Y)‖:=by congr 1;change x i*X-y i*Y=_;ring
      _≤‖(x i-y i)*X‖+‖y i*(X-Y)‖:=norm_add_le _ _
      _≤δ*(∏j∈s,B j)+B i*(δ*others s B):=by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul (fee i) bx (norm_nonneg _) non)
          (mul_le_mul (yp i) prior (norm_nonneg _) bi)
      _=_:=by ring

variable {V:Type}[DecidableEq V][Fintype V]{R:Census V}

def cost (x:Poly R)(δ:ℝ)(s:R.Mode):ℝ:=
  ∑p∈shards R s,‖mobiusTop p.val.card‖*others p.val (fun i=>‖x.part i.val‖+δ)

theorem original (x y:Poly R)(normalized:x.part R.quiet=1)(printed:y.part R.quiet=1)
    {δ:ℝ}(non:0≤δ)(fee:∀i:R.Mode,‖(x-y).part i‖≤δ)(s:R.Mode):
    ‖(connected x-connected y).part s‖≤δ*cost x δ s:=by
  rw [part_sub,log_partition x normalized,log_partition y printed,←Finset.sum_sub_distrib]
  unfold cost
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun p _=>?_ )
  rw [←mul_sub,norm_mul]
  have before (i:Multi.Hot R):‖x.part i.val‖≤‖x.part i.val‖+δ:=by linarith only [non]
  have after (i:Multi.Hot R):‖y.part i.val‖≤‖x.part i.val‖+δ:=by
    have bill:‖y.part i.val-x.part i.val‖≤δ:=by rw [norm_sub_rev];exact fee i.val
    calc ‖y.part i.val‖=‖x.part i.val+(y.part i.val-x.part i.val)‖:=by simp
         _≤‖x.part i.val‖+‖y.part i.val-x.part i.val‖:=norm_add_le _ _
         _≤_:=by linarith only [bill]
  have bill:=telescope p.val (fun i:Multi.Hot R=>x.part i.val) (fun i=>y.part i.val) _ non before after (fun i=>fee i.val)
  exact (mul_le_mul_of_nonneg_left bill (norm_nonneg _)).trans_eq (by ring)

end YM.Integration.WilsonCoherentMayerPriorPartitions

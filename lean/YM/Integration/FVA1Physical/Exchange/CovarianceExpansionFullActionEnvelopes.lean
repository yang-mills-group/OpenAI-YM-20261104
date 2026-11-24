import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFullPhysicalMask
import YM.Integration.KBoundGas
import YM.AllOrder.Laplace.Spin

/-! Finite native envelopes for the original and independently filed
geometric + passenger actions, including every rank-two local subtraction
and every signed tensor entry. These bounds are used only for integrability. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function MeasureTheory Finset Lattice RG Wilson Precision Push.Local
open AnalyticBridge VerifiedReset AllOrder.Laplace
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{k:ℕ}{ι:Type*}
local notation "Fld" => Config G n

private theorem contact_continuous (a:Atom G k)(z:Site n):Continuous (contactBody a (contactTrim a) z):=by
  change Continuous (fun U:Fld=>contactBody a (contactTrim a) z U)
  by_cases h:k=2
  · simp only [contactBody,if_pos h]
    fun_prop
  simpa only [contactBody,if_neg h] using a.unmasked_cont z

private theorem filed_env (p:BudgetPoint)(coef:ℝ)(A:ℕ→Atom G k){s C:ℝ}(sp:0<s)
    (stock:SumBudget (fun i=>(A i).budget s) C):
    Envelope (physicalPassenger A p coef (n:=n)):=by
  let c:=|VerifiedReset.factor*coef| *(2*((2:ℝ)^k))
  have cn:0 ≤ c:=by dsimp only [c];positivity
  let major:=fun r:Seat n×ℕ=>(A r.2).budget s*c
  have dom:Dominated (fun r:Seat n×ℕ=>filedSeat p coef (A r.2) r.1 (n:=n)):=by
    refine ⟨major,(ConnectedActivityE6.Raw.finite_start major (fun _=>(∑'i,(A i).budget s*c)) (fun _=>(stock.2.1.mul_right c).hasSum)).summable,?_⟩
    intro r W
    by_cases h:Healthy p.threshold (r.1.spread (contactSupport (A r.2) (contactTrim (A r.2)) 0)) W
    · simp only [filedSeat,masked_eq _ _ _ _ h,Real.norm_eq_abs,abs_mul]
      have atom:|(contactBody (A r.2) (contactTrim (A r.2)) 0 (r.1.view W))| ≤
          2*((A r.2).budget s*2^k):=(contact_body_bound (A r.2) (contactTrim (A r.2)) (0:Site n) (r.1.view W) (show (contactTrim (A r.2)).magnitude ≤ (A r.2).magnitude from le_rfl)).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((A r.2).lower_budget s sp) (by positivity)) (by norm_num))
      exact (mul_le_mul_of_nonneg_left atom (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (by dsimp only [major,c];rw [abs_mul];ring)
    simp only [filedSeat,masked_ne _ _ _ _ h,norm_zero]
    exact mul_nonneg (stock.1 _) cn
  refine ⟨Measurable.tsum ?_,dom.bound⟩
  intro r
  apply masked_measurable
  exact measurable_const.mul ((contact_continuous _ (0:Site n)).comp (continuous_pull r.1.1 r.1.2)).measurable

private theorem orbit_env (A:ℕ→Atom G k){s C:ℝ}(sp:0<s)(stock:SumBudget (fun i=>(A i).budget s) C):
    Envelope (wilsonOrbit A (n:=n)):=by
  unfold wilsonOrbit Patch.average
  exact (Envelope.const _).mul (Envelope.sum _ _ (fun i=>by
    have h:=env_uncut (n:=n) stock sp
    exact ⟨h.meas.comp (continuous_pull i 0).measurable,by
      obtain ⟨b,hb⟩:=h.cost;exact ⟨b,fun W=>hb (pull i 0 W)⟩⟩))

private theorem list_env (F:ι→Fld→ℝ)(L:List ι)(env:∀v∈L,Envelope (F v)):
    Envelope (fun W=>(L.map (fun v=>F v W)).sum):=by
  induction L with
  | nil=>exact Envelope.const 0
  | cons a l ih=>exact (env a List.mem_cons_self).add (ih (fun v hv=>env v (List.mem_cons_of_mem _ hv)))

theorem filed_action_envelopes (p:BudgetPoint)(c:Clip)(P:PathData G){s C Λ s' C':ℝ}
    (pay:P.Bounds c s C Λ)(β:ℝ)(rank:ι→ℕ)(A:(v:ι)→ℕ→Atom G (rank v))
    (coef:ι→ℝ)(L:List ι)(sp:0<s')(stock:∀v∈L,SumBudget (fun i=>(A v i).budget s') C'):
    Envelope (fullPhysical (n:=n) p c P β rank A coef L) ∧ Envelope (fullIndependent (n:=n) c P β rank A coef L):=
  ⟨(PathData.channels_env pay p β).add (list_env _ L (fun v h=>filed_env p (coef v) _ sp (stock v h))),
    (((Envelope.const β).mul (toll_main pay).fit).add (toll_loop pay).fit).add
      (list_env _ L (fun v h=>(Envelope.const _).mul (orbit_env _ sp (stock v h))))⟩

end YM.Integration.FVA1Physical.Exchange.ShieldedAction

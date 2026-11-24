import YM.RG05Readout.Pulse.Groups
/-!
# Patch polynomial cost layer
Support smooth in every tensor variable.Fin. Uses only global t-th derivative
 high for pure error with ANY anchor positions and corners. Mixed factorial
 as in `Work.G05`. Build near & project. No complex Cauchy bounds needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Nuclear
open Tensor Analysis Function Filter Set MeasureTheory Native Pulse
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n m d k:ℕ}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
local notation "J"=> Complexion E
section sum
lemma aboveD {p:Tensor.T E ℂ d} (hp:Tensor.Sym p)(h:d<n): iteratedFDeriv ℝ n (Tensor.diagonal p)=0:=by
    ext1 x; ext1 v
    induction d generalizing x n with
    | zero=> rw [show Tensor.diagonal p=(fun _=>Tensor.diagonal p 0) from funext (fun j=> congr_arg p (Subsingleton.elim ..))]; rw [iteratedFDeriv_const_of_ne h.ne']
    | succ d ih=>
       cases n with
       | zero=> exact (Nat.not_succ_le_zero _ h.le).elim
       | succ n=>
          rw [← Fin.cons_self_tail v, Analysis.cons_inner (diag_smooth p _|>.contDiffAt)]; let x':= v 0; let Y:=p.curryLeft x'; rw [show D x' (Tensor.diagonal p)=(↑(d+1:ℕ):ℝ) • Tensor.diagonal Y from funext (fun t=> (differential_diagonal p hp t x').trans (by rw [Pi.smul_apply,Nat.cast_smul_eq_nsmul]; rfl)),iteratedFDeriv_const_smul_apply (diag_smooth _ _|>.contDiffAt), smul_apply]; change ((↑(d+1:ℕ):ℝ)) • iteratedFDeriv ℝ n (Tensor.diagonal Y) x _ = 0; rw [show iteratedFDeriv ℝ n (Tensor.diagonal Y) x (Fin.tail v)=0 from ih (freeze_sym p hp x') (by omega) x _]; exact smul_zero _

def port (p:J)(d:ℕ):J:= ⟨Work.G05.blockTaylor d p.val,Work.G05.blockTaylor_contDiff d p.val ∞⟩
lemma shoots (i:ℕ)(p:J)(x:E)(r:ℝ)(y:E): iteratedFDeriv ℝ i (Pulse.fork r x p).val y=r^i • iteratedFDeriv ℝ i p.val (x+r • y):=by
   let g(z):=p.val (x+z); change iteratedFDeriv ℝ i (fun x=> g (r • x)) y=_
   rw [iteratedFDeriv_comp_const_smul r (show ContDiff ℝ i g from (lit p i).comp (contDiff_const.add contDiff_id))]; simp only [g]; rw [iteratedFDeriv_comp_add_left] -- d param remove
lemma fork_at (p:J)(n:ℕ)(x:E)(y:E):iteratedFDeriv ℝ n (fork 1 x p).val y= iteratedFDeriv ℝ n p.val (x+y):= by rw [shoots n,one_pow,one_smul,one_smul]
noncomputable def package (n:ℕ)(x:E)(p:J):J:= Pulse.fork 1 (-x) (port (Pulse.fork 1 x p) n)
lemma pol_cost (x:E)(p:J)(h:k≤ n): pie p (package n x p) k x:=by
    unfold pie package; rw [fork_at,neg_add_cancel,show (port _ _).val=Work.G05.blockTaylor n (fork 1 x p).val from rfl,Work.G05.blockTaylor_jets (lit _ _|>.contDiffAt) k h,fork_at,add_zero]
lemma pol_above (x:E)(p:J)(h:n<k): iteratedFDeriv ℝ k (package n x p).val=0:=by
    funext y; unfold package; let Y:= fork 1 x p; rw [fork_at,show (port _ _).val=Work.G05.blockTaylor n Y.val from rfl]; unfold Work.G05.blockTaylor; rw [iteratedFDeriv_sum_apply]; swap; · intro i _; exact (diag_smooth ..).contDiffAt
    exact Finset.sum_eq_zero fun j hj => congr_fun (aboveD (coeff_symm (lit Y _|>.contDiffAt)) ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans_lt h)) (-x+y)
lemma sphere (x:E)(p:J)(r C:ℝ)(hr:0≤ r)(hC:0≤C)(hp:∀ y,‖y-x‖≤r→ ‖iteratedFDeriv ℝ (n+1) p.val y‖≤ C) (i:ℕ)(h:i≤n+1)(y:E)(hy:‖y-x‖≤r):
    ‖iteratedFDeriv ℝ i (package n x p).val y-iteratedFDeriv ℝ i p.val y‖ ≤ C*r^(n+1-i):=by
    let Y:= package n x p; let Z:=Y-p
    have he(i:ℕ)(z:E) : iteratedFDeriv ℝ i Y.val z-iteratedFDeriv ℝ i p.val z=iteratedFDeriv ℝ i Z.val z:= (iteratedFDeriv_sub_apply (lit Y i|>.contDiffAt) (lit p i|>.contDiffAt)).symm
    rw [he i]; induction h using Nat.decreasingInduction generalizing y with
    | self=>
        rw [← he, show Y=package n x p from rfl,pol_above _ _ n.lt_succ_self, Pi.zero_apply,zero_sub,norm_neg, Nat.sub_self,pow_zero,mul_one]; exact hp y hy
    | of_succ j _ ih=>
        let f:=iteratedFDeriv ℝ j Z.val; set m:=n+1-(j+1); have hm:n+1-j=m+1:=by omega
        rw [hm,pow_succ,← mul_assoc]
        let T:= Metric.closedBall x r; have hx:x∈T:=Metric.mem_closedBall_self hr; have hτ:y∈T:=Metric.mem_closedBall.mpr (by rw [dist_eq_norm];exact hy)
        have ht: ‖f y-f x‖≤C*r^m *‖y-x‖:=by
           refine (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (fun z _=> (lit Z (j+1)|>.contDiffAt).differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr j.lt_succ_self)) (fun z hz=>?_ ) hx hτ
           rw [show ‖fderiv ℝ f z‖=‖iteratedFDeriv ℝ (j+1) Z.val z‖ from norm_fderiv_iteratedFDeriv]; exact ih z (by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hz)
        have hx : f x=0:=by unfold f; rw [← he, (pol_cost x p (show j≤ n by omega)).symm,sub_self]
        rw [hx,sub_zero] at ht; exact ht.trans (mul_le_mul_of_nonneg_left hy (by positivity))
-- recognition at any center
lemma abroad (x:E)(p:J)(hp:iteratedFDeriv ℝ (n+1) p.val=0): p= package n x p:=by
   apply Subtype.ext; funext y; have ht:= sphere x p ‖y-x‖ 0 (norm_nonneg _) le_rfl (fun z _=> by rw [hp]; simp) 0 (Nat.zero_le _) y le_rfl
   rw [zero_mul] at ht; have he:= sub_eq_zero.mp (norm_le_zero_iff.mp ht); simpa only [iteratedFDeriv_zero_apply] using (congr_arg (fun z:Tensor.T E ℂ 0 => z (fun _=>x)) he).symm
-- polynomial coordinate from P and q diff within ball
lemma congr_site {i:ℕ} (x y:E)(p:J)(h:i≤d)(r C:ℝ)(hx:0≤r)(hc:0≤C)(hp:∀ z:E, ‖iteratedFDeriv ℝ (d+1) p.val z‖ ≤ C)(hy:‖y-x‖≤r) :
     ‖iteratedFDeriv ℝ i (package d y p - package d x p).val x‖ ≤ C*r^(d+1-i):=by
    rw [show (package d y p-package d x p).val=(package d y p).val-(package d x p).val from rfl,iteratedFDeriv_sub_apply (lit _ _|>.contDiffAt) (lit _ _|>.contDiffAt),(pol_cost x p h).symm]; apply sphere y p r C hx hc (fun z _=> hp z) i (h.trans d.le_succ) x (by rw [norm_sub_rev]; exact hy)
end sum
end YM.RG05Readout.Nuclear

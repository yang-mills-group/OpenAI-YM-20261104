import YM.AllOrder.Gyro.Lift
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Gyro
open Function Filter Lattice RG Wilson Push Push.AbsoluteSums Precision AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration PhysicalNext MeasureTheory
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m:Side}{p:BudgetPoint}(d:RegularAddress n){f:Config G n→ℝ}(g:G.Simple)(H:p.Regular d.support f) (x y:Site n) (b:PlaqAxes)
open Averaging
variable {X : Listing G n}{v:Collection.Source G n}{Y : Listing G n}{u:Collection.Source G n}{c w c' w' β ζ η α:ℝ} (h:Collection.Local X p v c w)(h':Collection.Local Y p u c' w') (R:PathData G)(F:Clip)(ht:earlyValue X R F p v β ζ α=earlyValue Y R F p u β η α)
local notation "q"=>X.read v
local notation "Q"=>Y.read u
include h g
local notation "C"=> (Fintype.card (Site n):ℝ)
local notation "a"=> axes01
section lift
variable (h0:20<n.val)
include g h
lemma circle : ∑' i, meter (v.logRead i) b = -(∑ x:Site n,∑ y:Site n, coord x y b.val.1 ^2*(∑' i,logHessian (v.logRead i) (esc G b x) (esc G b y)))/2:= by
 let f i (x y:Site n):= coord x y b.val.1 ^2*logHessian (v.logRead i) (esc G b x) (esc G b y)
 have he x y : Summable fun i=>f i x y:= (scorebill g h b x y).mul_left _
 simp_rw [meter,tsum_div_const,tsum_neg]; change -(∑' i,∑ x,∑ y,f i x y)/2= _; rw [Summable.tsum_finsetSum (fun x _=> summable_sum fun y _=> he x y)]; simp_rw [Summable.tsum_finsetSum fun y _=> he _ y]; simp_rw [f,tsum_mul_left]
include h0
open Finset
lemma nucleus : |C*delta (q)-(∑' i, meter (v.logRead i) a)| ≤ C*(reward n p.threshold * vault n p c):= by
 obtain ⟨f,hf,hv⟩:= h.cheap
 let g₁ i:=projection (X.reg i) (v.logRead i) a a-meter (v.logRead i) a; let v₁ (x:Site n) i:= if (X.reg i).site=x then g₁ i else 0; let m x i:=if (X.reg i).site=x then meter (v.logRead i) a else 0
 have hh(x:Site n):= headline_p g h h0 hf hv x
 have he x: Summable (m x):= Summable.of_norm_bounded (mindset g h a).norm (fun i=>by unfold m; split; rfl; simp)
 have hp x: ∑' i,v₁ x i=delta (q) - ∑' i,m x i:= by
    have ht' i:v₁ x i=censusAt (q) x a a i-m x i:=by by_cases hX:(X.reg i).site=x<;>simp [v₁,g₁,hX,censusAt,Listing.read,m]; -- if vs decidable
    simp_rw [ht']; rw [(h.projects.seriesAt g a a x).tsum_sub (he x),show Averaging.delta _= total (q) x a a from (by rw [isotropic g h.projects (by omega) x h.transforms a a]; simp),Averaging.total]
 let T:= (C*delta (q) - (∑' i, meter (v.logRead i) a))
 have hi i: meter (v.logRead i) a=∑ x,m x i:= by unfold m; simp
 have hV : ∑ x:Site n, ∑' i,v₁ x i=T:= by unfold T; rw [funext hi,Summable.tsum_finsetSum (fun x _=> he x)]; -- type mismatch?
                                                 simp_rw [hp,Finset.sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul]
 rw [show C*Averaging.delta _- _= _ from hV.symm]; exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun x _=> hh x)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul]))
-- compared drift available for recovering exactly same Beta increment. At true Early price.
include h'
theorem schiz (hh : parallel X v Y u p):|delta (q) - delta (Q)| ≤ reward n p.threshold * vault n p (c+c'):= by
 have hx := nucleus g h h0; have he := nucleus g h' h0; let M:=∑' i,meter (v.logRead i) a
 have hv : (∑' i, meter (v.logRead i) a) = ∑' i,meter (u.logRead i) a:= by rw [circle g a h,circle g a h']; simp_rw [no_garb g a h h' hh]
 have hz:0<C:= by have hp:=Fintype.card_pos (α:=Site n); positivity
 rw [← hv] at he; apply le_of_mul_le_mul_left («a»:=C) _ hz; rw [← abs_of_pos hz,← abs_mul,mul_sub]; rw [show C*delta (q)-C*delta (Q)=(C*delta (q)-M)-(C*delta (Q)-M) by ring]; rw [abs_of_pos hz]; exact (abs_sub ..).trans ((add_le_add hx he).trans_eq (by unfold vault; ring))
end lift
end YM.AllOrder.Gyro

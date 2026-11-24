import YM.MSbar.Spruce.GlobalP
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Spruce
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Lapaz
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Kelvin Further.GaussianScalar
variable {ι σ τ: Type} [Fintype σ][DecidableEq σ] [Fintype ι][DecidableEq ι][Fintype τ][DecidableEq τ]
variable (f:Pot σ)(x: View σ)
local notation "μ"=>PowerSeries.coeff
noncomputable def dart (i:ℕ) (f:Pot σ): Pot σ:= Yarn i (fun L:List σ=> Whisk.read 0 L f • play L)
lemma darts (i:ℕ)(f:Pot σ): dart (i+1) f= ∑ j:σ,X j * dart i (pderiv j f):=by
     unfold dart; rw [twilled]; refine sum_congr rfl fun j _=>?_; have hv:= Whisk.spun (AddMonoidHom.mulLeft (MvPolynomial.X j:Pot σ)) i (fun L=> Whisk.read 0 L (pderiv j f) • play L); rw [show X j*_= _ from hv]; refine stitch i fun T _=>?_ ; change Whisk.read 0 T (pderiv j f) • (_*play T) = X j * (_ • play T); rw [mul_smul_comm]
lemma loses (i:ℕ)(f:Pot σ)(j:σ) : pderiv j (dart (i+1) f)=(i+1:ℝ) • dart i (pderiv j f):=by
     induction i generalizing f with
     | zero=> rw [darts,_root_.map_sum]; simp [dart,Yarn,play,Pi.single_apply, ite_mul]-- names
     | succ i ih=>
         rw [darts,_root_.map_sum]; simp_rw [pderiv_mul,sum_add_distrib]; rw [show (∑ x:σ,pderiv j (X x) * dart (i+1) (pderiv x f))= dart (i+1) (pderiv j f) from ?_ ]; swap; · simp [Pi.single_apply,ite_mul]; -- fix
         simp_rw [ih,seasoning j _,mul_smul_comm]; rw [← smul_sum,← darts]; push_cast; simp only [add_smul,one_smul]; abel
noncomputable def scores (i:ℕ)(f:Pot σ): Pot σ:= (i.factorial:ℝ)⁻¹ • dart i f
lemma boon(j:σ)(f:Pot σ)(p:ℕ): pderiv j (scores (p+1) f)=scores p (pderiv j f):=by unfold scores; rw [Derivation.map_smul, loses, smul_smul]; congr 1; rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]; field_simp
lemma testk : (MvPolynomial.eval x) (dart 0 f)= eval (0:View σ) f:=by rw [dart,twillz]; let r:=eval (0:View σ) f; change MvPolynomial.eval x (r • 1)=_; change aeval x (r • (1:Pot σ))=_; rw [map_smul,map_one,smul_eq_mul,mul_one]
lemma tagB {f g:Pot σ}(h: (MvPolynomial.eval (0:View σ)) f=MvPolynomial.eval 0 g)(hp:∀ i:σ,pderiv i f=pderiv i g): f=g:=by
    apply MvPolynomial.funext; intro i; -- MvPolynomial.funext vars
    obtain ⟨u,he,ht⟩:= Bakery.cutAt (x:=0) (y:=i) (f:=fun x=>eval x (f-g)) [] (convex_univ) (Set.mem_univ _) (Set.mem_univ _) (fun x _=> (vent _).contDiffAt.of_le le_top)
    have he(i:σ) : glance (fun i=>eval i (f-g)) [i] u=0:=by rw [glance_jet, Whisk.read_next,_root_.map_sub,hp i,sub_self,map_zero]
    change (eval i (f-g))-(eval 0 (f-g))=∑ i':σ, _ at ht; rw [map_sub,map_sub,h,sub_self,sub_zero] at ht; apply sub_eq_zero.mp; refine ht.trans (sum_eq_zero (fun j _=>?_)); rw [List.nil_append, show glance _ _ _=0 from he j, mul_zero] -- verify append
noncomputable def ropes (p:ℕ)(f:Pot σ):Pot σ:= ∑ i∈ Finset.range (p+1),scores i f
lemma tape (f:Pot σ)(i:ℕ)(he:f.totalDegree ≤ i): ropes i f=f:=by
     have ht(j): pderiv j (scores 0 f)=0:=by simp [scores,dart,Yarn,play]
     apply tagB
     · unfold ropes; rw [map_sum,Finset.sum_eq_single_of_mem 0 (mem_range.mpr (Nat.succ_pos i))]; · simp only [scores,Nat.factorial_zero,Nat.cast_one,inv_one,one_smul]; exact testk f _
       intro j hj hc; obtain ⟨j,rfl⟩:= Nat.exists_eq_succ_of_ne_zero hc; unfold scores; change MvPolynomial.aeval (0:View σ) (_ • _)=_; rw [map_smul,darts,_root_.map_sum]; rw [sum_eq_zero (fun i _=>?_ ),smul_zero]; rw [map_mul,MvPolynomial.aeval_X]; exact zero_mul _
     intro x; cases i with
     | zero=> have h:f.totalDegree=0:=Nat.eq_zero_of_le_zero he; simp only [ropes,zero_add,sum_range_one,ht]; rw [totalDegree_eq_zero_iff_eq_C.mp h,pderiv_C]
     | succ i=> unfold ropes; rw [_root_.map_sum, Finset.sum_range_succ',ht]; simp only [add_zero]; simp_rw [boon]; exact tape (pderiv x f) i (Cacao.pdeg x he)
termination_by i
end YM.MSbar.Spruce

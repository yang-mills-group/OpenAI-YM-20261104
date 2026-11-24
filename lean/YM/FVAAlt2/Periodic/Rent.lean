import YM.Comparison.RG02.Bulk.Sequence
import YM.Push.FREE_RESOLVENT.Test
import YM.Progress.JOINT_CALENDAR.Germs
/-!
# Matching by R's actual station and book D0

Retaining Kin. NO claim the Curvature path can be selected differently. Rather, **exactly at all admitted periods** (in this Chain) its tagged-main/Curved Hessian is fixed across successive steps by the level/cutoff identity at stop; this data is enough to identify each actual quadratic (before any periodic approximation). Bind by *finite* Comptroller. Works even with nonlinear body, with Hessian sym in color basis. Does not assert low rank e=2 one-loop after rewash.
 Note: similar to `RG08.Port` Scene & Agora for alternate score, derived here for the actual path (reuse F03/F04 analysis).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Period.Rent
open Filter Set MeasureTheory Function Finset Lattice Tree RG Precision Wilson Matrix Bloch Laurent Pressure Bid Stores Exterior
open Comparison.RG02 Comparison.RG02.Bulk Work.F03 Work.F04 Progress.Joint
open scoped Topology ContDiff Classical Matrix.Norms.Frobenius BigOperators ENNReal InnerProductSpace Matrix
variable {c f n : Side}{G:Gauge}{S:StepData c f}{P:PathData G}{ζ:ChartRatio G}
variable {J₁ J₂ : Clip}{A B:ℝ}

def Right (p:Clip)(P:PathData G) (n:Side) (C:Bed): Prop:= ∀ x y: Bid.Dir G n, iteratedFDeriv ℝ 2 (mainTerm p P ∘ represent (G:=G)) 0 ![x,y] = gaugeFiscal C x y

attribute [local instance] Gauge.frobInner
lemma swapped (C:Bed) (h:(C.metric.acts n)ᵀ=C.metric.acts n) (x y:Dir G n): gaugeFiscal C x y=gaugeFiscal C y x:=by
  unfold gaugeFiscal
  have he:( Precision.K (C.metric.acts n))ᵀ= Precision.K (C.metric.acts n):=by unfold Precision.K;rw [transpose_mul,transpose_mul,h,transpose_transpose,Matrix.mul_assoc]
  refine sum_congr rfl (fun i _=>?_ ); set M:=Precision.K (C.metric.acts n); rw [←he,dotProduct_transpose_mulVec]; rw [he]
lemma control_top (C : Bed)(J: Clip) (hp : SameJet (X:=Dir G n) 2 (mainTerm J P ∘ represent) (Wilson.energy ∘ represent) ) (hc:C.diagonal.acts n=1)(hh:Floor C J₂ n A B) : Right J P n C:= by
   intro i j; rw [hp.2.2]; exact ( hessian_of_limit (Q:= fun x y:Dir G n=> gaugeFiscal C x y) (hp.2.1.of_le le_top) (fun x=>energy_limit C x hh hc) gaugeFiscal_add (swapped C hh.symmetric.1) ).2.2 ..
variable (K:Bulk.Kernel S J₁ P ζ) (C D:Bed) (H: Right J₁ P f C)
local notation "V"=> (mainTerm J₁ P ∘ represent (n:=f))
local notation:max "M_" t:max => (flat S t J₁ P)
include H K
lemma moving_line (x:Dir G f): Tendsto (fun t:ℝ=>mainTerm J₁ P (represent (t • x))/t^2) (𝓝[≠] 0) (𝓝 (gaugeFiscal C x x/2)):= by
    obtain ⟨a,A,L,hB⟩:= K.bounds
    have hf: ContDiffAt ℝ 2 V 0:= (Extra.Iteration.Calibration.main_jet hB).of_le le_top
    have hg:fderiv ℝ V 0=0:= main_first (m:=f) _ _ hB
    rw [← H x x,← line_second hf hg]; let u(t:ℝ):= t • x; have hz:u 0=0:=zero_smul ..; refine taylor_limit_two (f:=(V)∘ u) ?_ ?_ ?_
    · exact (show ContDiffAt ℝ 2 V (u 0) by rw [hz];exact hf).comp 0 (by unfold u; fun_prop)
    · rw [Function.comp_apply,hz]; exact main_origin (m:=f) _ _ hB
    change deriv (fun t:ℝ=> V (t • x)) 0=0; rw [(Push.side V (hf.differentiableAt (by simp)) x).deriv,hg]; rfl
include K
lemma controller (F:Forest S.ratio) : Comptroller F C J₁ P:=by
   obtain ⟨a,A,L,hB⟩:= K.bounds
   let C':= Extra.Iteration.Calibration.main (n:=f) P J₁
   have hf: ContDiffAt ℝ 2 V 0:= (Extra.Iteration.Calibration.main_jet hB).of_le le_top
   have he: ∀ x y:Dir G f,gaugeFiscal C x y=gaugeFiscal C y x:=fun x y=> ((H x y).symm.trans (hessian_symmetric hf x y)).trans (H y x)
   intro k T; have hs:ContDiffAt ℝ 2 (flat S k J₁ P) 0:= (flat_smooth K.branches k (Work.F02.answer _ _ _ _ _ _ hB)).of_le le_top
   have hz:= from_flat (S:=S) F k P J₁
   have hh: ∀x: Logs G c f,Tendsto (fun t:ℝ=> M_ k (t • x)/t^2) (𝓝[≠] 0) (𝓝 (flatHess S C x x/2)):=by
      intro x; simp_rw [flat, flatHess, add_div]; exact (moving_line K C H x.2).add (noise_limit K.branches k x)
   have ha:∀ x y z: Logs G c f,flatHess S C (x+y) z=flatHess S C x z+flatHess S C y z:=by
     intro x y z
     have hw : bills S (x.2+y.2) = bills S x.2 + bills S y.2 := by ext i j; simp only [bills, parts_add, mulVec_add, Pi.add_apply]; rfl
     have he' : residual S (x+y) = residual S x + residual S y := by unfold Work.F03.residual; simp only [Prod.fst_add,Prod.snd_add,hw]; abel
     simp only [flatHess, Prod.snd_add, gaugeFiscal_add, he', Pi.add_apply, inner_add_left, Finset.sum_add_distrib, mul_add]; abel
   have hsy:∀ x y:Logs G c f, flatHess S C x y=flatHess S C y x:=by
     intro x y; unfold flatHess; congr 1
     · exact he ..
     congr 1; exact Finset.sum_congr rfl fun _ _=> real_inner_comm ..
   obtain ⟨hv,h1,h2⟩:= hessian_of_limit (Q:=fun x y:Logs G c f=> flatHess S C x y) hs hh ha hsy
   have hd:= hessian_comp (f:=M_ k) (inclusion_zero F) hs ((inclusion_smooth F).of_le le_top) h1; refine ⟨ origin _ _ _ F k hB K.branches,hz.fderiv_eq.trans hd.1,fun w v=>?_ ⟩
   unfold T; rw [(hz.iteratedFDeriv ℝ 2).eq_of_nhds,hd.2,inclusion_deriv F,inclusion_deriv F,h2]; rfl
variable (Q:Matrix (Body 1 f) (Body 1 c) ℝ)(hq: Inputs S Q (C.metric.acts f) (D.metric.acts c))
include hq
lemma initiative (F:Forest S.ratio)(x:Dir G c): fderiv ℝ (K.b F) 0 x = relative F Q x := by
    obtain ⟨η,hp,he⟩:=K.gap F; exact Work.F04.tangent F _ _ η hp he C D Q hq (controller K C H F) (K.b F) (K.critical F) (Classical.arbitrary _) x
lemma cruise {P':PathData G} (F:Forest S.ratio)(h: ClassicalMatch F J₁ J₂ P P' (K.b F) ) : Right J₂ P' c D :=by
    let U:=K.b F
    let t: S.Choices:= Classical.arbitrary _
    let W:= Function.uncurry (tested F t J₁ P)
    let b(x:Dir G c):=(x,U x)
    intro x y; change iteratedFDeriv ℝ 2 (fun x=> mainTerm J₂ P' (represent x)) 0 ![x,y]=_; rw [← (h 2 (by decide) t).2.2]
    have hh:=K.critical F
    have hu:b 0=0:=by unfold b U; simp [hh.1]
    have hv :HasFDerivAt b ((ContinuousLinearMap.id ℝ (Dir G c)).prod (fderiv ℝ U 0)) 0 := (hasFDerivAt_id 0).prodMk (hh.2.1.differentiableAt (by simp)).hasFDerivAt
    have Ht:=controller K C H F; have he :fderiv ℝ b 0 y=(y,relative F Q y):=by rw [hv.fderiv, ContinuousLinearMap.prod_apply]; rw [show fderiv ℝ U 0 y=_ from initiative K C D H Q hq F y]; rfl
    change iteratedFDeriv ℝ 2 (W ∘ b) 0 _= _
    rw [(hessian_comp (f:=W) hu ((hh.2.2 t).1.of_le le_top) (( contDiffAt_id.prodMk hh.2.1 ).of_le le_top) (Ht t|>.2.1)).2, he, hv.fderiv]; exact Work.F04.test_pair F _ _ C D Q hq Ht _ y t
-- Prec paid here. Panel in this chart equals full precision projected slot.
omit hq
open FreeResolvent
lemma honest (F:Forest S.ratio)(t:S.Choices): hessian F t J₁ P 0 0 = treeMatrix G S F C.metric:=by
   exact FreeResolvent.Tests.checked_loop F C t _ _ (fun t=> ((K.critical F).2.2 t).1) (controller K C H F)
-- Occupied force. measure μ Φ epoch ages are not hypotheses of this
end YM.FVAAlt2.Period.Rent

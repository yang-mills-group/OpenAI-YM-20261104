import YM.OPE.Compatible.Glow.Ramp
import Mathlib.Analysis.Calculus.SmoothSeries
/-! Density reading and finite smooth torus -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
variable {P:I→ Chant G n}{x:I→ℝ}{v:fieldX (Shade G)}{N:Side}
def rhythm (P:I→ Chant G n)(x:I→ℝ)(v:CoverConfig G):= ∑' i,x i*verseX (P i) v
lemma staffQ (v:fieldX (Shade G))(hp:Quiet v 0):∃ k:ℝ,0 ≤ k∧∀ i: Edge Cover,‖indexS i v‖≤ k:=by
    obtain ⟨C,hc,H⟩:=hp; refine ⟨(Fintype.card G.ColorIndex:ℝ)*C,by positivity,fun i=>?_⟩; let A:=indexS i v; let e:=EuclideanSpace.basisFun G.ColorIndex ℝ; change ‖A‖≤_
    have he(j:G.ColorIndex): ‖e.repr A j‖ ≤ C:=(H (i.1,i.2,j)).trans_eq (by unfold poise;ring)
    nth_rw 1 [← e.sum_repr A]; apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun _=> C) (fun i _=> by rw [norm_smul,OrthonormalBasis.norm_eq_one,mul_one]; exact he i)).trans_eq; simp
lemma rimline (h:saturate P x s U)(hs:0<s)(hg:∀ i,moderateX (P i) D)(hy:0≤D)(k:ℕ)(hp:Quiet v 0): WardBin.leading k (fun t:ℝ=> rhythm P x (lotU (t • v))) = wholeX (timbre P x k) fun _=>v:=by
    let f(i:I)(t:ℝ):=x i * verseX (P i) (lotU (t • v)); have he(i):ContDiff ℝ ∞ (f i):=contDiff_const.mul (cash_smooth _ v |>.of_le le_top)
    obtain ⟨z,hz,H⟩:=staffQ v hp; choose c hc hh using fun j=>cashBill G n s z D hs hz hy j
    let A(j)(i):=c j*(‖x i‖*Real.exp (s * lawn (P i))); have hP(j):Summable (A j):=h.2.1.mul_left _
    let g(i:I)(t:ℝ):=verseX (P i) (lotU (t • v))
    have hx(j:ℕ)(i t):iteratedFDeriv ℝ j (f i) t=x i • iteratedFDeriv ℝ j (g i) t:=by change iteratedFDeriv ℝ j (x i • g i) t=_; exact iteratedFDeriv_const_smul_apply ((cash_smooth (P i) v).contDiffAt.of_le le_top) -- API
    have hV(j:ℕ)(i:I)(t):‖iteratedFDeriv ℝ j (f i) t‖≤ A j i:=by
       rw [hx,norm_smul,norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact (mul_le_mul_of_nonneg_left (hh j _ _ (hg i) (fun a _=>H a) t) (norm_nonneg _)).trans_eq (by unfold A;ring)
    change WardBin.leading k (fun t=>∑' i,f i t)=_
    have heq: WardBin.leading k (fun t=>∑' i,f i t)=∑' i,x i * WardBin.leading k (g i):=by
        unfold WardBin.leading iteratedDeriv; rw [iteratedFDeriv_tsum_apply he (fun k _=> hP k) (fun k i j _=> hV k i j) le_top]; rw [show (∑' (n:I), iteratedFDeriv ℝ k (f n) 0) (fun _=>1)=(∑' n,iteratedFDeriv ℝ k (f n) 0 (fun _=>1)) from (ContinuousMultilinearMap.apply ℝ _ _ (fun _:Fin k=>(1:ℝ))).map_tsum ((hP k).of_norm_bounded (fun i=> hV k i 0))]; simp_rw [hx]; simp only [_root_.smul_apply,smul_eq_mul]; rw [← tsum_mul_left]; apply tsum_congr; intro i; ring
    rw [heq]; unfold g; simp_rw [coinShots]; exact (everyone h hg hs hy _ (k:=fun _:Fin k=>0) (fun _=> hp)).tsum_eq
-- torus log with shift
abbrev upl {T:Type*} {N:Side}(x:Site N)(v: deck T N):fieldX T:=fun i=>v (x+wrap N i.1,i.2)
lemma expoS (h:deck (Shade G) N)(x:Site N): expandAt x (fun j=> G.lieExp (indexS (lift j.1,j.2) (upl 0 h)))= lotU (upl x h):=by
    ext1 i; unfold expandAt lotU; apply congr_arg G.lieExp; ext j; change h (0+wrap N (lift (wrap N i.1+x)),_)= _; rw [wrap_lift,zero_add,add_comm];rfl
abbrev primU (G:Gauge)(v:deck (Shade G) N): Config G N:=fun j=> G.lieExp (indexS (lift j.1,j.2) (upl 0 v))
lemma timing (p: Script W r)(x:Site N) (v:Fin r→ deck W N): wholeX p (fun i=>upl x (v i))=scribe x p v:=rfl
lemma rimTurn (h:saturate P x s U)(hp:∀ i,moderateX (P i) D) (hs:0<s)(hd:0≤ D)(v: deck (Shade G) N)(z:Site N): WardBin.leading r (fun t:ℝ=> rhythm P x (expandAt z (primU G (t • v))))= value z (timbre P x r) v:=by
    rw [show (fun t:ℝ=> rhythm P x (expandAt z _))= (fun t:ℝ=> rhythm P x (lotU (t • upl z v))) from funext fun i=> by erw [expoS];rfl]; exact rimline h hs hp hd r ⟨‖v‖,norm_nonneg _,fun i=>(norm_le_pi_norm v _).trans_eq (by unfold poise;ring)⟩
end Script
end YM.OPE.Flume

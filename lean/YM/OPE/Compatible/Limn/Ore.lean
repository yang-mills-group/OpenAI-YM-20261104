import YM.OPE.Compatible.Limn.Vase
/-!
# Regression via shelves. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Limn
open Function Filter Set MeasureTheory Lattice Laurent RG Matrix Precision Exterior Tree Push Push.AbsoluteSums Wilson Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{c f:Side}
open Next.SectorChange Next.SectorChange.Schur PertExtension Series Libra GaussianScore Flume Flume.Page Flume.Script Flume.Virgin Zeph
open AnalyticNext.QuarticMatch Radius Estimate Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom AnalyticNext.QuarticMatch.Local
open Cascade Rill Votive Stationary Progress.StationaryScenes Work.F03 Next.Free Work.F05 Glass Coin Pilot Next.Foundations Work.F08 FreeResolvent
open PhysicalNext.Repeat.Aroma
variable {r R B b ε X:ℝ}{m:ℕ}
variable (S:StepData c f)(H:Odd S.ratio.count.val)
open Finset Module
open Green (wt)
local notation "F"=> forest S.ratio H
local notation "Wκ"=> Wings G c
local notation "Q"=> (Bid.Dir G c × AxisChart G F)
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u:ℝ}
variable (A:Alps K T i v)(U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g:Bid.Dir G c→ AxisChart G (forest S.ratio H)}(k:S.Choices)
variable (V:FibreRep S H U k A g b)(h:licensed S H U A.clip A.live L A.sky g)
local notation "Σ!"=>pane F k A.clip A.live
local notation "Q!"=> Key F G
noncomputable def PyramidQ :Matrix (Key F G) (Wings G c) ℝ:= Matrix.of fun i j=> Bitush S F Σ! (.inr i) (.inl j)
lemma bitsread (y:Key F G)(j:Wings G c):PyramidQ S H A k y j = iteratedFDeriv ℝ 2 Σ! 0 ![(0,countingBasis F G y), (JetB G c j,0)]:=by unfold PyramidQ Bitush MintS; rw [Matrix.of_apply,Basis.prod_apply,Basis.prod_apply,Sum.elim_inl,Sum.elim_inr];rfl
include V h
lemma Copp (x:Bid.Dir G c): (FUND S H U)*ᵥ(cash (countingBasis F G) (V.L.M x))= -((PyramidQ S H A k)*ᵥ cash (JetB G c) x):=by
       let P:= Σ!; let B:= V.L; let H':=iteratedFDeriv ℝ 2 P 0; let D:=FUND S H U; let Z:=countingBasis F G; funext i; let z:=Z i; change (D *ᵥ _) i = - _
       let u:=(x,(0:AxisChart G F)); let a:=((0:Bid.Dir G c),z); let v:=((0:Bid.Dir G c),B.M x); have hy:H' ![(x,B.M x),a]=0:=by unfold B; rw [V.M,← folds k h.2.1]; exact (viewer k h.2.1).hedge ..
       have hz: H' ![a,(x,B.M x)]=0:=(Work.F03.hessian_symmetric ((viewer k h.2.1).origin.of_le le_top) ..).trans hy
       have hm: H' ![a,u]+H' ![a,v]=0:=by rw [show H' ![a,u]+H' ![a,v]=H' ![a,u+v] from (DFunLike.congr_fun ((H'.curryLeft a).curryLeft.map_add u v) ![]).symm, show u+v=(x,B.M x) from Prod.ext (add_zero _) (zero_add _)]; exact hz
       have hp:H' ![a,v]=(D *ᵥ (cash (countingBasis F G) (B.M x))) i:=by erw [tollY S H U h k, cashOne];simp; rfl
       let j := JetB G c; let Q':=PyramidQ S H A k; let E:Bid.Dir G c→ Q:= fun p=>(p,0); have hU : u=(ContinuousLinearMap.inl ℝ _ _ :Bid.Dir G c→L[ℝ] Q) (∑ s, cash j x s • j s):= congr_arg (ContinuousLinearMap.inl ℝ (Bid.Dir G c) (AxisChart G F)) (j.sum_repr x).symm; let T':= ContinuousLinearMap.inl ℝ (Bid.Dir G c) (AxisChart G F); have hS:H' ![a,u]=(Q'*ᵥ cash j x) i :=by
            rw [hU]; change (H'.curryLeft a).curryLeft (T' _) ![]= _; rw [map_sum T',map_sum (H'.curryLeft a).curryLeft,_root_.sum_apply]; refine sum_congr rfl (fun k' _=>?_); rw [T'.map_smul,(H'.curryLeft a).curryLeft.map_smul]; change cash j x k'*H' ![a,T' (j k')] = _*_; rw [_root_.mul_comm]; congr 1; exact (bitsread S H A k i k').symm
       rw [hS,hp] at hm; exact eq_neg_of_add_eq_zero_left (by rw [add_comm];exact hm)
noncomputable def LiftM (U:Boxes G S.patch S.kernel): Matrix (Key F G) (Wings G c) ℝ:= -((FUND S H U)⁻¹ * PyramidQ S H A k)
lemma Rvoice (x:Bid.Dir G c): cash (countingBasis F G) (V.L.M x)=(LiftM S H A k U) *ᵥ cash (JetB G c) x:=by
       let D:= FUND S H U; have hp : IsUnit D.det := (D.isUnit_iff_isUnit_det).mp (ulk_force ..).isUnit
       unfold LiftM; rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_neg, ← Copp S H A U k V h, mulVec_mulVec,Matrix.nonsing_inv_mul _ hp, one_mulVec]
omit V h
lemma trim_c (t:ℝ)(ht:0<t){p:Site f→(Bid.Dir G c×AxisChart G (forest S.ratio H))→ℝ}(hB:0≤ R)(he:0<ε)(hx:Dew.Pile S F ε R t m Σ! p)(hm:2 ≤ m):Pours (PyramidQ S H A k) (pointK S F) (cotW S (G:=G)) (t/2/2) (max (farm G (t/2/2)) (creep G (t/2/2))*(R*Premium.overall (t/2))):=by
          refine Schur.pure (half_pos ht) (mul_nonneg hB (zero_le_one.trans (Premium.cover_ge _))) (fun i j=>lensM ht hB he hx hm (.inr i) (.inl j)) (farmPay S F (half_pos (half_pos ht))) (oro S (half_pos (half_pos ht)))
end YM.OPE.Limn

import YM.OPE.Compatible.Gully.Piece
/-!
# Scored cubic
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.StageLight
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Radial Flume.Script
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
attribute [local instance] Gauge.frobInner
variable {n m:Side}{G:Gauge}{C:RG.KernelChoices}{r:ℕ}
variable {i:ℕ}{l b:ℝ}{B:Sponsor G} {Q:Seasons B}{A:Alps B Q i l}{H:Even n.val}{P:ChartRatio G}
local notation "TK"=> Keys G (Limb H)
lemma noM (hg:G.Simple): fderiv ℝ (mural H A) 0=0:=by
   ext u; have hh:= (h_disc H A hg).base1 u; unfold jet at hh; norm_num [iteratedFDeriv_one_apply] at hh; rw [fderiv_sub ((muralD ..).differentiableAt (by simp)) (differentiableAt_const _)] at hh; simpa using hh
lemma noF (hg:G.Simple): fderiv ℝ (gilt H A) 0=0:=by
     have hk: A.liftZ 1=0:= A.soft_leaf hg; have hz:fderiv ℝ (swornY A.live (n:=n)) 0=0:=by
         ext x; rw [← show iteratedFDeriv ℝ 1 (swornY A.live) 0 ![x]=fderiv ℝ (swornY A.live) 0 x from iteratedFDeriv_one_apply .. ]; have hh:= (A.fullL 1).wink n 1 le_rfl ![x]; rw [hk] at hh; exact (show _ = _ from hh.symm).trans (by simp [library,scribe])
     let f:=swornY A.live (n:=n); let L:= cloak H (G:=G); have hp:DifferentiableAt ℝ f (L 0):=by rw [map_zero]; exact ((A.fullL 1).plot n).differentiableAt (by simp)
     unfold gilt; simp_rw [div_eq_mul_inv]; rw [fderiv_mul_const (hc:= _)]; swap; · exact hp.comp _ L.differentiableAt -- f hint
     change (4:ℝ)⁻¹ • fderiv ℝ (f ∘ L) 0=0; rw [fderiv_comp _ hp L.differentiableAt, map_zero, show fderiv ℝ f 0=_ from hz]; simp
lemma blankTint (Y:Lit H A b)(hg:G.Simple)(x:TK): jet Y.s.w 1 x=0:=by
    have hp: ContDiffAt ℝ ω (gilt H A) 0:=by
         let L:=cloak H (G:=G); exact (((L.map_zero.symm ▸ (A.fullL 1).plot n : ContDiffAt ℝ ω (swornY A.live) (L 0)).comp _ L.contDiff.contDiffAt).div_const 4)
    have hg':=noF (A:=A) (H:=H) hg; have ht:=noM (A:=A) (H:=H) hg
    have hf: DifferentiableAt ℝ (-(b:ℝ) • mural H A) 0:= ((muralD H A).const_smul (-b)).differentiableAt (by simp); let T:= (-(b:ℝ) • mural H A)-gilt H A
    unfold jet; rw [iteratedFDeriv_one_apply,Y.light.fderiv_eq, show tintT H A b= Real.exp ∘ T from rfl, fderiv_comp 0 Real.differentiableAt_exp (hf.sub (hp.differentiableAt (by simp))), show fderiv ℝ T 0=0 from ?_]; simp
    unfold T; rw [fderiv_sub hf (hp.differentiableAt (by simp)),fderiv_const_smul ((muralD H A).differentiableAt (by simp)),hg',ht];simp
lemma prizeW (Y:Lit H A b)(x:TK) (hp:Track A n):jet Y.s.f 3 x=(G.colorScale^2*8)⁻¹ * scribeX (exclaim H x) (exclaim H x) (exclaim H x):=by
    let L:=hippie H (G:=G); rw [← dataX x hp]; have hv:ContDiffAt ℝ (↑(3:ℕ):WithTop ℕ∞) (mural H A) 0:=(muralD H A).of_le le_top
    unfold jet; congr 1; rw [(Y.uplift.iteratedFDeriv ℝ 3).eq_of_nhds,iteratedFDeriv_add_apply (show ContDiffAt ℝ (↑(3:ℕ):WithTop ℕ∞) (_ - fun (_:TK)=>mural H A 0) 0 from hv.sub contDiffAt_const) ((hSm H|>.contDiffAt).of_le le_top),iteratedFDeriv_sub_apply hv contDiffAt_const,iteratedFDeriv_const_of_ne (by norm_num)]; simp only [Pi.zero_apply,sub_zero, _root_.add_apply]; rw [show (iteratedFDeriv ℝ 3 L 0) (fun _=>x) = 0 from ?_, add_zero]
    rw [show (iteratedFDeriv ℝ 3 L 0) (fun _=>x)= _ from (iteratedDeriv_on_line (k:=3) (hSm H|>.contDiffAt.of_le le_top) x).symm]; simp_rw [h_degree]; erw [iteratedDeriv_mul_const_field,iteratedDeriv_fun_pow_zero]; simp -- tactic
lemma price_ink (Y:Lit H A b)(h:G.Simple)(p:LocalRatio P)(hp:Track A n)(x:TK): (Y.s.hat P x).l= -(G.colorScale^2*8)⁻¹ * scribeX (exclaim H x) (exclaim H x) (exclaim H x):=by rw [coldPeak p,blankTint _ h,prizeW Y x hp]; ring
end YM.OPE.StageLight

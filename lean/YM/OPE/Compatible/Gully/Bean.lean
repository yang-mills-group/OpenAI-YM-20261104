import YM.OPE.Compatible.Gully.Sit
import YM.OPE.Compatible.Begun.Vigor
import YM.OPE.Compatible.Chain.Badges
/-!
# Bare kernel identity.Intercept
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stubble
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch Further.FreeCovariance.KP MSbar.Tree MSbar.Tree.Resolvent Terp
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
attribute [local instance] Gauge.frobInner
variable {n:Side}{G:Gauge}{C:RG.KernelChoices}{r:ℕ}
open Pert.Full (char toroid)
open Balsam
lemma twineX (p:Site n)(i): mon p i=(Pert.Full.moment p i:ℂ):=by
   change (n.val:ℂ)⁻¹*(2 * (Real.pi:ℂ)*(Lattice.lift p i:ℂ)) = _; rw [Pert.Full.moment_apply]; unfold Pert.Full.mesh; push_cast; ring
lemma tonal (p x:Site n): cell p x=char p x:=by
     obtain ⟨y,rfl⟩:∃ y,wrap n y=x:=⟨_,wrap_lift _⟩
     rw [cell_wrap,Pert.Full.char_wrapped]; unfold mode Pert.Full.corner; push_cast; congr 1; simp_rw [twineX]; ring_nf; congr 1; apply Finset.sum_congr rfl; intro i _; ring
lemma molt (p:Site n):MSbar.Tree.Torus.lap (mon p)=Pert.Full.delta (Pert.Full.moment p):=by
     unfold MSbar.Tree.Torus.lap Pert.Full.delta; apply Finset.sum_congr rfl; intro i _; unfold Exterior.q; rw [twineX,Complex.norm_exp_I_mul_ofReal_sub_one]; simp only[Real.norm_eq_abs,sq_abs,mul_pow]; ring
lemma molly (v: Site n)(h:4≤ r): spline (ShellRow C (Train.top r)) (mon v)= (MSbar.Tree.Torus.lap (mon v):ℂ) • 1:=by -- RG.Kernel??
   rw [spline_char _ h _ (real_frequency v)]; have ht:=mon_mem n v; rw [show (pink _ _).read (mon v)=_ from (heart_true C.penalty C.penalty_pos h (Train.top r)).1.echo (mon v) ht, (top_metric _ C.penalty_pos r (base_subset_realCube zone_pos ht)).2]; simp only [outside,Matrix.mul_one]; exact Torus.hessian_gf _
lemma slender_m (p:Site n)(h:4≤ r): slender (ShellRow C (Train.top r)) p=(↑(MSbar.Tree.Torus.lap (mon p)):ℂ)⁻¹ • 1:=by
    unfold slender; split
    next hp=>subst p;simp [Torus.lap,q]
    next hh=>
     rw [molly p h]; have he:=Complex.ofReal_ne_zero.mpr (Torus.positive p hh).ne'; let s:ℂ:=MSbar.Tree.Torus.lap (mon p); apply Matrix.inv_eq_right_inv
     rw [Matrix.smul_mul, Matrix.mul_smul,Matrix.one_mul, smul_smul,mul_inv_cancel₀ he,one_smul]
lemma strip_field (h:4≤r)(u v:Site n)(i j:TypeFace 1): lineC (ShellRow C (Train.top r)) n (u,i) (v,j)=if i=j then mildX [] (u-v) else 0:=by
     unfold lineC realOf; rw [Matrix.map_apply,spectral_apply]; by_cases he:i=j
     · subst j; rw [if_pos rfl,mild_tip,toroid]; congr 1; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun p hp=>?_); rw [slender_m p h,Matrix.smul_apply,one_apply,if_pos rfl,smul_eq_mul,mul_one,tonal,Pert.Full.topWeight]; unfold Further.FreeCovariance.KP.meter; rw [molt p,_root_.zpow_neg,zpow_ofNat];ring
     rw [if_neg he]; simp_rw [fun p=> slender_m (C:=C) (n:=n) p h,Matrix.smul_apply,one_apply,if_neg he];simp
lemma spilling (h:4 ≤ r)(i j: TypeFace 1)(a:Cover): Spill C (Train.top r) h i j a=if i=j then hull [] (-a) else 0:=by
      let U:= twin (2:Side); have he:= old_coin (r:=r) U.sides (C:=C) (.top r) h i j a (fun n=>0); simp_rw [vein,strip_field h] at he; apply tendsto_nhds_unique he
      split_ifs
      next hp=>
           simp only [zero_add,zero_sub,← map_neg]; apply calm _ _ U.sides; filter_upwards with i; exact Even.mul_right (show Even (2:Side).val from ⟨1,rfl⟩) ((2:Side)^i).val
      next hp=> exact tendsto_const_nhds
end YM.OPE.Stubble

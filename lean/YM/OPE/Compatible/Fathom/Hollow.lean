import YM.OPE.Compatible.Vino.Cut
import YM.OPE.Compatible.Fathom.Cycle
/-!
# Tensor Schur identity
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d:ℕ}{K:KernelChoices}
local notation "I!"=> Body 1 n
lemma filed (n:Side) : approached (Resolvent.missing n)= spectral (m:=n) (fun p=> if p=0 then 1 else 0):=by
       ext ⟨u,i⟩ ⟨v,j⟩; unfold approached; rw [Matrix.map_apply, Resolvent.projected,spectral_apply, Finset.sum_eq_single 0] -- `meter`
       · rw [if_pos rfl,Matrix.one_apply,cell_duality,cell_origin,one_mul]; by_cases he:i=j
         · rw [if_pos he,if_pos he,mul_one]; push_cast; rfl
         simp [he]
       · intro k _ he; rw [if_neg he]; simp
       simp
lemma lamVoid (C:KernelChoices)(v:Train r)(n:Side): Resolvent.missing n* lineC (ShellRow C v) n=0:=by
       unfold lineC; rw [← realOf_mul,filed,spectral_mul]; ext ⟨x,i⟩ ⟨y,j⟩; rw [realOf,Matrix.map_apply,spectral_apply,Finset.sum_eq_zero]; simp; intro v _; by_cases h:v=0;rw[if_pos h];simp [h,slender]; rw [if_neg h]; simp
lemma lamMe (n:Side): Resolvent.missing n*Resolvent.missing n=Resolvent.missing n:=by
       change Resolvent.missing n* realOf (spectral _) = _; rw [← realOf_mul,filed,spectral_mul]; unfold Resolvent.missing; congr 2; funext p;split<;>simp
lemma lamK (C:KernelChoices)(v:Train r)(n:Side)(h:4 ≤ r): major (ShellRow C v) n*Resolvent.missing n=0:=by
       unfold Resolvent.missing; rw [← realOf_mul,medic _ (Op_whole h v), spectral_mul]; ext ⟨u,i⟩ ⟨v',j⟩; rw [realOf, Matrix.map_apply,spectral_apply,Finset.sum_eq_zero]; simp; intro k _; by_cases he:k=0; subst k;simp [knot C h v]; rw[if_neg he]; simp
abbrev Shrink (C:KernelChoices)(G:Gauge)(v:Train r)(n:Side):= tensor G (major (ShellRow C v) n+Resolvent.missing n)
abbrev CloakX (G:Gauge)(n:Side):=tensor G (Resolvent.missing n)
abbrev CapeV (C:KernelChoices)(G:Gauge)(v:Train r)(n:Side):= PhV C v G n+CloakX G n
open AnalyticBridge.LocalGaussianLaws.Current
lemma cloakR (C:KernelChoices)(v:Train r)(G:Gauge)(n:Side)(h:4 ≤ r): Shrink C G v n*CapeV C G v n=1:=by
       have hu : (major (ShellRow C v) n+Resolvent.missing n)*(lineC (ShellRow C v) n+Resolvent.missing n)=1:=by rw [mul_add, add_mul,add_mul,(neutralize n h v).1,lamVoid,lamMe,lamK C v n h]; abel
       unfold Shrink CapeV PhV CloakX; rw [← AnalyticBridge.LocalGaussianLaws.Current.tensor_add,← AnalyticBridge.LocalGaussianLaws.Current.tensor_mul,hu]; apply Matrix.ext_of_mulVec_single; intro i; rw [one_mulVec]; funext x; obtain ⟨x,j,q⟩:=x; change component (tensor G (1:Matrix (Body 1 n) _ ℝ) *ᵥ _) q (x,j)= component (Pi.single i 1) q (x,j); rw [component_mul,one_mulVec]
lemma cloakPos (C:KernelChoices)(v:Train r)(G:Gauge)(n:Side)(h:4 ≤ r): (Shrink C G v n).PosSemidef:=by
      let P:= major (ShellRow C v) n; let X:= P+Resolvent.missing n; let M:= (pink C.penalty v).acts n
      have hK:P.PosSemidef:=by unfold P major; rw [Op_stays h v]; exact Matrix.PosSemidef.add (KF v h) (by rw[← conjTranspose_eq_transpose_of_trivial];exact Matrix.posSemidef_self_mul_conjTranspose _)
      have hP:X.PosSemidef:= by refine Matrix.PosSemidef.add hK ?_; rw [← lamMe, show _* _= (Resolvent.missing n)*(Resolvent.missing n)ᴴ from (by rw[conjTranspose_eq_transpose_of_trivial,misSym])]; exact Matrix.posSemidef_self_mul_conjTranspose _ -- unde?
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v=>?_
      · unfold IsHermitian Shrink; rw [conjTranspose_eq_transpose_of_trivial,tensor_transpose]; have hh:=hP.1.eq; rw [conjTranspose_eq_transpose_of_trivial] at hh; rw[hh] -- X defeq?
      rw[star_trivial,component_dot];unfold Shrink; simp_rw [component_mul]; exact Finset.sum_nonneg fun i _=> by simpa only [star_trivial] using hP.dotProduct_mulVec_nonneg (component v i)
lemma cloakElite (C:KernelChoices)(v:Train r)(G:Gauge)(n:Side)(h:4 ≤ r): (Shrink C G v n).PosDef:=by
       apply ((cloakPos C v G n h).posDef_iff_isUnit).mpr; let V:=CapeV C G v n; have he : Shrink C G v n*V=1:=cloakR C v G n h -- need h arg
       exact ⟨⟨_,V,he,mul_eq_one_comm.mp he⟩,rfl⟩
-- Π matrix exact plus Ψ. 
end YM.OPE.Cascade.Paver

import YM.OPE.Compatible.Plains.Shire
import YM.OPE.Compatible.Plains.Gene
import YM.OPE.Compatible.LevelX.Tol
/-!
# Semidefinite PhV. ordinary finite purchase chamber. duplicated angle legs
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell FreeResolvent Paver Rill
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{U:Gloam}{d k j r w e:ℕ}{I:Type}[Fintype I]
lemma aboutM (n:Side): approached (missing n)=spectral (m:=n) (fun p=> if p=0 then 1 else 0):=by
    ext ⟨u,i⟩ ⟨v,j⟩; rw [show approached (missing n) _ _=(missing n (u,i) (v,j):ℂ) from rfl,projected,spectral_apply,Finset.sum_eq_single 0]; swap; · intro l _ hl; rw [if_neg hl];simp
    swap; · simp
    rw [if_pos rfl,one_apply]; by_cases he:i=j
    · rw [if_pos he,if_pos he, cell_duality,cell_origin]; simp [Further.FreeCovariance.KP.meter]
    rw [if_neg he,if_neg he];simp
lemma vanished (n:Side):missing n*Resolvent.pre n=0:=by
     unfold Resolvent.pre; rw [← realOf_mul,aboutM,spectral_mul]; rw [show (fun _=>_)= (fun (_: Site n)=> (0:Matrix (TypeFace 1) (TypeFace 1) ℂ)) from ?_]; swap
     · funext i; by_cases he:i=0
       · subst i; simp [Torus.lap,q]
       rw [if_neg he,zero_mul]
     ext ⟨x,a⟩ ⟨y,b⟩; simp [realOf,spectral_apply]
lemma cotSem (h:4≤r): (Cot L G (Train.top r) N).PosSemidef:=by
     let p:= Train.top r; let M:=Cot L G p N; let Z:= major (ShellRow L p) N; let C':=PhV L p G N; let T:=OrderR G N; rw [spotON]
     have hz : lineC (ShellRow L p) N=Resolvent.pre N:=by unfold Resolvent.pre lineC; apply congr_arg; apply congr_arg; exact funext (fun i=> slender_m i h)
     have he:(Resolvent.pre N)ᵀ=(Resolvent.pre N):=pre_symm N; let A:=Resolvent.pre N
     have hp:A.PosSemidef:=by
         let Cn:= neutralize (C:=L) N h p; obtain ⟨hh,h⟩: Z*A=1-missing N ∧ A*Z=1-missing N:=by rw [show A=lineC _ N from hz.symm];exact Cn
         rw [show A=Aᴴ *Z*A from ?_]
         · exact (show Z.PosSemidef from Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (pondT (C:=L) ‹4≤r› p N) fun i=>by rw [star_trivial]; exact basin_nonneg ‹4≤r› p i).conjTranspose_mul_mul_same ..
         simp only [Matrix.conjTranspose_eq_transpose_of_trivial,show Aᵀ=A from he,h]; rw [sub_mul,one_mul,show _*A=0 from vanished N,sub_zero]
     have hQ:C'.PosSemidef:= by
          unfold C' PhV; rw [hz]; apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (show (tensor G A).IsHermitian from by
            ext ⟨x,b,u⟩ ⟨v,w,s⟩; erw [Matrix.conjTranspose_apply]; rw [star_trivial]; change (if s=u then A _ _ else 0)=(if u=s then A _ _ else 0); by_cases ht:s=u; rw [if_pos ht,if_pos ht.symm]; exact congrFun (congrFun he (x,b)) (v,w); rw [if_neg ht,if_neg (Ne.symm ht)])
          intro x; rw [star_trivial, component_dot]; simp_rw [component_mul]; exact Finset.sum_nonneg fun i _=>by simpa only [star_trivial] using hp.dotProduct_mulVec_nonneg (component x i)
     exact hQ.mul_mul_conjTranspose_same T
open scoped MatrixOrder in
lemma realise (M:Silt.Mat I)(hm:M.PosSemidef):∃ (A: Law (EuclideanSpace ℝ I))(Z:EuclideanSpace ℝ I→L[ℝ] PAD I), M= chamber A Z:=by
    obtain ⟨B,hB⟩:= CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hm.nonneg
    let X:= EuclideanSpace ℝ I; let D:=Bᵀ; have he:M=D*Dᵀ:=by rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at hB; rw [hB]; simp [D]
    let P:X→ₗ[ℝ] Module.Dual ℝ X:={ toFun x:= (innerSL ℝ x).toLinearMap,map_add' x y:= LinearMap.ext fun z=>inner_add_left (𝕜:=ℝ) x y z,map_smul' x y:=LinearMap.ext fun z=>real_inner_smul_left y z x }
    have hp(x:X):P x x=‖x‖^2:=real_inner_self_eq_norm_sq x
    let T:= Law.mk P (fun x y=> real_inner_comm y x) ⟨1/2,(by norm_num),fun i=>le_of_eq (by rw [hp];ring)⟩ (by simp_rw [hp];fun_prop)
    let E:X→L[ℝ] PAD I:=(PiLp.continuousLinearEquiv 2 ℝ (fun _=> ℝ)).toContinuousLinearMap
    let Z:= Silt.climbs D ∘L E; have hx(i j:I):T.wick (coQ Z i) (coQ Z j)= (D*Dᵀ) i j:=by
          let v:= toLp 2 (fun k=>D i k); have ht: coQ Z i=P v:=LinearMap.ext (fun u=> by change (Z u) i=inner ℝ v u; erw [PiLp.inner_apply]; change (∑ k,D i k*u k)=_; exact Finset.sum_congr rfl (fun i _=>by unfold v; erw [RCLike.inner_apply]; exact mul_comm .. ))
          unfold Law.wick; rw [ht,show _= _ from Law.solves T v]; change (D *ᵥ (fun k=>D i k)) j=_; rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun b _=> mul_comm ..
    refine ⟨T,Z,?_⟩; rw [he]; ext i j; exact (hx i j).symm
end YM.OPE.Prairies

import YM.OPE.Compatible.Glim.Fade
/-! # orbit derivative Ward and stencil bases -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell
variable {I J E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype I](p:I)
variable (b:Bool)(a:G.Color)(S:Score I J)
local notation "U!"=> G.Color
local notation "E!"=> Keys G I
open Score
-- valid germ envelope
abbrev Pier (x:G.Color):Prop:= Pip G b (0,x)=x ∧ ContDiffAt ℝ ω (Pip G b) (0,x) ∧ ∀ᶠ z in 𝓝 (0,x),G.lieExp (Pip G b z)=Grip G b z
noncomputable abbrev lunge(x:E!): G.Color→L[ℝ] E!:= ContinuousLinearMap.single ℝ (fun _:I=>G.Color) p ∘L sword b (x p)
noncomputable abbrev waveL (x:E!)(u:G.Color): E!:= Function.update x p (Pip G b (u,x p))
omit [Fintype I] in lemma soon(x:E!)(h:Pier b (x p)): waveL p b x 0=x:=by unfold waveL; rw [h.1]; exact update_eq_self ..
omit [Fintype I] in
lemma lungeA(x:E!)(h:Pier b (x p)): HasFDerivAt (waveL p b x) (lunge p b x) 0:=by
     apply hasFDerivAt_pi''; intro i; by_cases ht:i=p
     · subst i; let Z:=Pip G b; let T:U!→U!×U!:=fun a=> (a,x p); have he:HasFDerivAt T (ContinuousLinearMap.inl ℝ U! U!) 0:= (hasFDerivAt_id (0:U!)).prodMk (hasFDerivAt_const _ _); have hv : HasFDerivAt (fun u=> waveL p b x u p) (sword b (x p)) 0 :=by simp_rw [waveL,update_self]; exact ((show ContDiffAt ℝ ω Z (T 0) from h.2.1).differentiableAt (by simp)).hasFDerivAt.comp (0:U!) he
       convert! hv using 1; ext1 u; change (lunge p b x u) p= _; unfold lunge; simp
     have he: (fun u=> waveL p b x u i)=fun _=>x i:=funext fun t=>update_of_ne ht ..; rw [he]; change HasFDerivAt _ (ContinuousLinearMap.proj i ∘L lunge p b x) _; rw [show ContinuousLinearMap.proj i ∘L lunge p b x =0 from ?_]; exact hasFDerivAt_const _ _
     ext1 v; change lunge p b x v i = 0; simp [lunge, Pi.single_eq_of_ne ht]
set_option maxHeartbeats 200000 in
omit [Fintype I] in lemma wink {x y:E!}(h:Pier b (x p))(he:Pier b (y p))(u:Tile G J)(hz:S.dress u (put x)=put y):
      ∀ᶠ z:G.Color in 𝓝 0,S.dress u (put (waveL p b x z))= put (waveL p b y (G.adjoint (u (S.start (p,b))) z)):=by
          let A:= (G.adjoint (u (S.start (p,b)))).toContinuousLinearMap; have hg:Tendsto (fun a:G.Color=>(a,x p)) (𝓝 0) (𝓝 (0,x p)):=Continuous.tendsto (continuous_id.prodMk continuous_const) (0:U!); have hp : Tendsto (fun a:G.Color=>(A a,y p)) (𝓝 0) (𝓝 (0,y p)):= by simpa using! (A.continuous.prodMk continuous_const|>.tendsto (0:U!)) -- specify
          filter_upwards [hg.eventually h.2.2,hp.eventually he.2.2] with t hT hV; funext i; by_cases ht:i=p
          · subst i; unfold Score.dress; change u (S.inn p)*G.lieExp (Function.update x p (Pip G b (t,x p)) p)*(u (S.out p))⁻¹=G.lieExp (Function.update y p (Pip G b (A t,y p)) p); rw [update_self,update_self, show G.lieExp (Pip G b (t,_))= _ from hT, show G.lieExp (Pip G b (A t,_))=_ from hV]; unfold Grip; erw [← show u _*G.lieExp (x p)*_ = G.lieExp (y p) from congr_fun hz p]; have hh:= Edict t b (u (S.inn p)) (u (S.out p)) (G.lieExp (x p)); cases b <;>exact hh.symm
          change _*G.lieExp (Function.update x p _ i) * _=G.lieExp (Function.update y p _ i); rw [update_of_ne ht,update_of_ne ht]; exact congr_fun hz i
variable {p b S}
noncomputable abbrev DColor (b:Bool)(p:I)(f:Keys G I→E)(x: Keys G I):G.Color →L[ℝ] E:= fderiv ℝ f x ∘L lunge p b x
lemma brake {x y:E!}(h:Pier b (x p))(he:Pier b (y p))(u:Tile G J)(hz:S.dress u (put x)=put y)(v:E!→E)(hp:ContDiffAt ℝ ω v x)(hv:ContDiffAt ℝ ω v y)(C:E→L[ℝ] E)(hw:∀ x y,S.dress u (put x) = put y → v y=C (v x)):
    DColor b p v y ∘L ((G.adjoint (u (S.start (p,b)))).toContinuousLinearMap)= C ∘L DColor b p v x:=by
       let A:=lunge p b x; let F:=lunge p b y; let T:= (G.adjoint (u (S.start (p,b)))).toContinuousLinearMap; have h1:HasFDerivAt (v ∘ waveL p b x) (fderiv ℝ v x ∘L A) 0:=by
            apply HasFDerivAt.comp _ (f:=waveL p b x) _ (lungeA p b x h); rw [soon p b x h]; exact (hp.differentiableAt (by simp)).hasFDerivAt
       have h2: HasFDerivAt (v ∘ waveL p b y) (DColor b p v y) (T 0):=by
            rw [T.map_zero]; apply HasFDerivAt.comp _ (f:=waveL p b y) _ (lungeA p b y he); rw [soon p b y he]; exact (hv.differentiableAt (by simp)).hasFDerivAt -- implicit
       apply (h2.comp (0:U!) T.hasFDerivAt).unique; apply (C.hasFDerivAt.comp (0:U!) h1).congr_of_eventuallyEq; exact (wink p b S h he u hz).mono fun i hi=> hw _ _ hi
end YM.OPE.Variance

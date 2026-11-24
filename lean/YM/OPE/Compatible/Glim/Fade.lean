import YM.OPE.Compatible.Glim.Yell
/-! # link differential as CL and transport -/
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
variable (b:Bool)(a:G.Color)
local notation "U!"=> G.Color
local notation "E!"=> Keys G I
noncomputable abbrev Grip (G:Gauge) (b:Bool)(z:G.Color×G.Color):= Spark b (G.lieExp z.1) (G.lieExp z.2)
noncomputable abbrev Pip(G:Gauge)(b:Bool)(z:G.Color×G.Color):G.Color:= G.plog (G.mat (Grip G b z))
lemma puck (G:Gauge)(b): ContDiffAt ℝ ω (Pip G b) 0:=by
   have he: (G.mat ∘ Grip G b) 0=1:=by simp only[Function.comp_apply]; unfold Grip; cases b<;>simp [Spark]
   have hz : ContDiff ℝ ω (G.mat ∘ Grip G b):=by cases b<;>simp only[Grip,Function.comp_def,Spark,Bool.false_eq_true,↓reduceIte,Homeomorph.coe_mulLeft,Homeomorph.coe_mulRight,G.mat_mul]; exact (G.exp_jet.comp contDiff_fst).mul (G.exp_jet.comp contDiff_snd); simp only [G.mat_inv]; exact (G.exp_jet.comp contDiff_snd).mul ((starL ℝ (A:=G.Mat)).contDiff.comp (G.exp_jet.comp contDiff_fst))
   exact ContDiffAt.comp (g:=G.plog) (f:=G.mat ∘ Grip G b) _ (he.symm ▸ G.plog_diff) hz.contDiffAt
lemma treat (G:Gauge)(b): ∀ᶠ x:G.Color in 𝓝 0,Pip G b (0,x)=x ∧ ContDiffAt ℝ ω (Pip G b) (0,x) ∧ ∀ᶠ z in 𝓝 (0,x),G.lieExp (Pip G b z)=Grip G b z:=by
    let X:= Grip G b; have he: Continuous X:=by unfold X; cases b; exact (G.lieExp_cont.comp continuous_fst).mul (G.lieExp_cont.comp continuous_snd); exact (G.lieExp_cont.comp continuous_snd).mul (G.lieExp_cont.comp continuous_fst).inv
    have h:X 0=1:=by unfold X Grip;cases b<;>simp [Spark]
    let T:= ContinuousLinearMap.inr ℝ G.Color G.Color; have hT:Tendsto T (𝓝 0) (𝓝 0):= T.map_zero ▸ T.continuous.tendsto 0; have hp : ∀ᶠ z in 𝓝 0,G.lieExp (Pip G b z)=X z:= (show Tendsto X (𝓝 0) (𝓝 1) from h ▸ he.tendsto 0).eventually G.plog_right
    filter_upwards [hT.eventually ((puck G b).eventually (by simp)),hT.eventually (eventually_eventually_nhds.mpr hp),G.plog_left] with x hx hv ht; refine ⟨?_,hx,hv⟩; change G.plog (G.mat (X (0,x)))=x; rw [show X (0,x)=G.lieExp x from ?_,ht]; unfold X Grip; cases b<;>simp [Spark]
noncomputable abbrev sword (b:Bool)(x: G.Color): G.Color →L[ℝ] G.Color := fderiv ℝ (Pip G b) (0,x) ∘L ContinuousLinearMap.inl ..
lemma tops {x:G.Color}(h: ContDiffAt ℝ ω (Pip G b) (0,x)): Cast b a x=sword b x a:=by
    let p:= Pip G b; let T:ℝ×G.Color→L[ℝ] U!×U!:= (((ContinuousLinearMap.id ℝ ℝ).smulRight a) ∘L (ContinuousLinearMap.fst ℝ ℝ U!)).prod (ContinuousLinearMap.snd ℝ ℝ U!)
    have hv:T (0,x)=(0,x):=by simp [T]
    unfold Cast tug sway; change fderiv ℝ (p ∘ T) (0,x) (1,0)= _; rw [fderiv_comp (0,x) (hv.symm ▸ h.differentiableAt (by simp) : DifferentiableAt ℝ p (T (0,x))) T.differentiableAt,T.fderiv,ContinuousLinearMap.comp_apply,hv, show T (1,0)=(a,0) from by simp [T]];rfl -- def
lemma CastSign : Cast b a 0= if b then -a else a:=by
   let u:=tug b a; have hp:= sky u (tug_live b a); apply hp.unique; -- Goal??
   let x(i:ℝ):= i • (if b then -a else a); have ht:HasDerivAt x (if b then -a else a) 0:=by unfold x; simpa using! ((hasDerivAt_id' (0:ℝ)).smul_const (if b then -a else a))
   apply ht.congr_of_eventuallyEq; filter_upwards [(show Tendsto x (𝓝 0) (𝓝 0) from by simpa [x] using! ht.continuousAt.tendsto).eventually G.plog_left] with i hi
   unfold u tug; rw [show snap b a (i,0)=G.lieExp (x i) from ?_]; exact hi
   unfold snap x; cases b <;>simp [Spark,exp_negative]
lemma cage (s:G.El)(u:G.Color) : G.lieExp (G.adjoint s u)=s*G.lieExp u*s⁻¹:=by apply G.mat_injective; rw [G.mat_lieExp,G.mat_adjoint,G.exp_conjugate,G.mat_mul,G.mat_mul, G.mat_lieExp]; rfl
lemma Edict (b:Bool)(s t u:G.El): Spark b (G.lieExp (G.adjoint (if b then t else s) a)) (s * u * t⁻¹) = s * Spark b (G.lieExp a) u * t⁻¹:=by rw [cage]; unfold Spark; cases b<;>simp only[↓reduceIte, Homeomorph.coe_mulLeft,Homeomorph.coe_mulRight,Bool.false_eq_true]<;>group
end YM.OPE.Variance

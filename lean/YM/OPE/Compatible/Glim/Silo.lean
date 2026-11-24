import YM.OPE.Compatible.Glim.Vera
/-! # Sum weight, Ward, and coordinate legs -/
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
noncomputable abbrev keyD(x:E!):=Pip G b (0,x p)
variable {w i j:ℕ}
local notation "B"=> Phone G
omit [Fintype I] in lemma lungePo (i:Keys G I)(h:Pier b (i p)): (lunge p b i) a=∑ j,tou p B b a j i • An p B j:=by
    let u: G.Color→L[ℝ] E!:= ContinuousLinearMap.single ℝ (fun _:I=>G.Color) p; change u (sword b (i p) a)=_; rw [← tops b a h.2.1]; let v:=Cast b a (i p); nth_rw 1 [←(Phone G).sum_repr (Cast b a (i p))]; rw [map_sum]; apply sum_congr rfl; intro i _; exact map_smul u _ _
local notation "Lf"=> Tested.germ
lemma lanceM (j:ℕ)(v:Keys G I→ℝ)(x:ℝ→ Keys G I)(hx:Gael x)(hp:ContDiffAt ℝ ω v 0)(h:Hush v j): Reads (fun t:ℝ=> ((t^j)⁻¹*t)*DColor b p v (t • x t) a) (Mining (Topper p a b (Pawn.mold v j)) x):=by
      let y(t:ℝ):=t • x t; let Y:=Mount p a b; let Ψ:=An p B; let r:=Pawn.mold v j; have hY:Tendsto y Lf (𝓝 0):=by unfold y; simpa using! (nhdsWithin_le_nhds (s:=Ioi (0:ℝ))|>(fun h=>(show Tendsto (fun i:ℝ=>i) Lf (𝓝 0) from h).smul ((Gael.oath hx).limit))) -- maybe Simp
      let P(j):= Y j *Pry (Ψ j) r; let f(i:G.ColorIndex)(t:ℝ):= tou p B b a i (y t)*( ((t^j)⁻¹*t)*bat (Ψ i) v (y t)); have ht(i:G.ColorIndex):Reads (f i) (Mining (P i) x):=by
           unfold P; rw [MiningM _ _ _ (tallJ _ _) (pryB _ _ (tallJ _ _)) hx]; exact (retire continuous_one (Pawn.calm ((CharterS p a b (Phone G) i).of_le le_top)) hx).pile (PryRead j v hp h _ x hx)
      apply (MiningU P univ f x hx (fun i _=>height (tallJ _ _) (pryB _ _ (tallJ _ _))) (fun i _=> ht i)).cong; filter_upwards [((continuous_apply p).continuousAt.tendsto.comp hY).eventually (treat G b)] with t ht; rw [Finset.sum_apply]; unfold f; change _ *(fderiv ℝ v (y t) (lunge p b (y t) a))= _; rw [lungePo p b a _ ht,map_sum,mul_sum]; apply sum_congr rfl; intro i _; rw [map_smul,smul_eq_mul]; unfold bat; ring
lemma CLMoment {W:E→L[ℝ] E}[FiniteDimensional ℝ E](u:Module.Basis I ℝ E):duty u W=LinearMap.trace ℝ E W.toLinearMap:=by rw [LinearMap.trace_eq_matrix_trace ℝ u]; unfold duty; simp only[Matrix.trace,LinearMap.toMatrix_apply,diag_apply]; rfl
variable {p b S}
set_option maxHeartbeats 200000 in
lemma cappe {t: G.El}{A A': G.Color→L[ℝ] G.Color} (h:A∘L ((G.adjoint t).toContinuousLinearMap)=((G.adjoint t).toContinuousLinearMap)∘L A'): duty B A= duty B A':=by
     let S:=(G.adjoint t).toContinuousLinearMap; let T:=(G.adjoint t⁻¹).toContinuousLinearMap; have hv:T∘L S=1:=by ext1 p; change G.adjoint t⁻¹ (G.adjoint t p)= p;rw [← G.adjoint_mul];simp
     have he:S ∘L T=1:=by ext1 p; change G.adjoint t (G.adjoint t⁻¹ p)=p;rw[← G.adjoint_mul];simp
     let K:=S ∘L A'; have hJ: A= K ∘L T:= by rw [← show A∘L S=K from h]; ext1 p; change A p=A (S (T p)); rw [show S (T p)=p from DFunLike.congr_fun he p];
     rw [hJ,CLMoment,CLMoment]; let M:= A'.toLinearMap ∘ₗ T.toLinearMap; change LinearMap.trace ℝ G.Color (S.toLinearMap ∘ₗ M)= _; rw [LinearMap.trace_comp_comm']; apply congr_arg; apply LinearMap.ext; intro i; change A' (T (S i))= A' i; rw [show T (S i)=i from DFunLike.congr_fun hv i]
end YM.OPE.Variance

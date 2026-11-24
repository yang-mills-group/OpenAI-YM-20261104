import YM.OPE.Compatible.Glim.Test
/-! # equivariance & force on finite cover -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F05
open Flock Libra.Shell Next.Foundations
variable {I J E F:Type}[Fintype I][Fintype J][NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
noncomputable def Flick (T:I≃J)(x:I→Bool): Keys G J→L[ℝ] Keys G I:= ContinuousLinearMap.pi fun i:I=> if x i then -(ContinuousLinearMap.proj (T i)) else ContinuousLinearMap.proj (T i)
omit [Fintype I][Fintype J] in lemma FlickP (T:I≃J)(x:I→Bool)(y:Keys G J)(i:I): Flick T x y i= if x i then -y (T i) else y (T i):=by unfold Flick; simp only[ContinuousLinearMap.pi_apply]; split <;>rfl
lemma swordV (b:Bool): ∀ᶠ x:G.Color in 𝓝 0,∀ v:G.Color,sword (!b) (-x) v= -(sword b x v) :=by
     let u(z:G.Color×G.Color):=Pip G (!b) (z.1,-z.2); have he : u=ᶠ[𝓝 0] fun v=>-(Pip G b v):=by
          let Q(z:G.Color×G.Color):=(z.1,-z.2); have ht: Q 0=0:=by unfold Q; simp
          have hp:=treat G b; have hq:=treat G (!b); have hz:Pier b (0:G.Color):=hp.self_of_nhds; have hh:Pier (!b) (0:G.Color):=hq.self_of_nhds; have hb:Tendsto Q (𝓝 0) (𝓝 0):=by have hu:Tendsto Q (𝓝 0) (𝓝 (Q 0)) := (continuous_fst.prodMk continuous_snd.neg).tendsto 0; rw [ht] at hu; exact hu
          have hv:Tendsto (fun z:G.Color×G.Color=>-(Pip G b z)) (𝓝 0) (𝓝 0):=by
               have hm:Pip G b 0=0:= hz.1; have hv: Tendsto (fun z:G.Color×G.Color=>-(Pip G b z)) (𝓝 0) (𝓝 (-Pip G b 0)):= hz.2.1.continuousAt.neg.tendsto; rw [hm,neg_zero] at hv; exact hv
          filter_upwards [hz.2.2,hv.eventually G.plog_left] with z h1 h3 -- may rewrites
          apply Eq.trans _ h3; unfold u Pip; -- target Pip expanded on RHS
          rw [exp_negative, show G.lieExp _=_ from (show G.lieExp (G.plog (G.mat (Grip G b z)))= _ from h1)]; apply congr_arg; apply congr_arg; unfold Grip; dsimp only; cases b <;> simp [Spark,exp_negative]
     let S:= ContinuousLinearMap.inr ℝ G.Color G.Color; have ht:Tendsto S (𝓝 0) (𝓝 0):= S.map_zero ▸ S.continuous.tendsto 0
     have hp:Tendsto (fun x:G.Color=> -x) (𝓝 0) (𝓝 0):=by simpa using continuous_neg.continuousAt.tendsto (x:=(0:G.Color))
     filter_upwards [ht.eventually (eventually_eventually_nhds.mpr he), hp.eventually (treat G (!b))] with x hx hh v
     let p:G.Color×G.Color→L[ℝ] G.Color×G.Color:= (ContinuousLinearMap.fst ℝ G.Color G.Color).prod (-(ContinuousLinearMap.snd ℝ G.Color G.Color))
     have hg:=EventuallyEq.fderiv_eq (𝕜:=ℝ) (show Pip G (!b) ∘ p=ᶠ[𝓝 (0,x)] (-(Pip G b)) from hx)
     unfold sword
     rw [fderiv_comp _ (g:=Pip G (!b)) (f:=p) (hh.2.1.differentiableAt (by simp)) p.differentiableAt,p.fderiv, fderiv_neg] at hg
     have hk:= DFunLike.congr_fun hg (v,0); change fderiv ℝ (Pip G (!b)) (0,-x) (p (v,0))=_ at hk; rw [show p (v,0)=(v,0) from by simp [p]] at hk; exact hk
-- linear universality.Avail Fe.
lemma moldC (L:E→L[ℝ] F)(f:F→ℝ)(h:ContDiffAt ℝ ω f 0)(i:ℕ):Pawn.mold (f ∘ L) i=(Pawn.mold f i)∘ L:=by
     funext x; have hh(j):jet (f ∘ L) j x=jet f j (L x):=by unfold jet; rw [jets_linear L (h.of_le le_top)];rfl
     exact eta _ _ (hh _) (hh _) (hh _)
lemma HushL (L:E→L[ℝ] F)(f:F→ℝ)(h:ContDiffAt ℝ ω f 0)(i:ℕ)(ht:Hush f i): Hush (f∘ L) i:=by intro x j hj; exact (show _=_ from (congr_arg JetS.s (congr_fun (moldC L f h j) x))).trans (ht (L x) _ hj)
end YM.OPE.Variance

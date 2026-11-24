import YM.OPE.Compatible.Glim.Silo
/-! # density root Wood.Mon.Opep -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Drift
open Flock Libra.Shell
variable {I J E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype I](p:I)
variable (b:Bool)(a:G.Color)(S:Score I J)
local notation "U!"=> G.Color
local notation "E!"=> Keys G I
open Score
local notation "B"=> Phone G
local notation "μ"=> Tested.germ
noncomputable def Cake (f g:E!→ℝ)(Y:E!→U!)(r:ℕ): ScriptJ E!:=
      ∑ i:G.ColorIndex, LoopM p ((Phone G) i) b (Pawn.mold f 2) (Pawn.mold g 0) (Pawn.mold ((Phone G).coord i ∘ Y) r)
lemma CakeB (f g:E!→ℝ)(Y:E!→U!)(r:ℕ): ScriptJ.B (Cake p b f g Y r):= by
    apply sumBat; intro i _; exact stampL _ _ _ (fun _ _=>tallJ _ _) _ _ (ScriptJ.key (tallJ _ _) (tallJ _ _)) (tallJ _ _)
protected structure Cand (r:ℕ)(Y:E!→U!):Prop where
     smooth : ContDiffAt ℝ ω Y 0
     silent (i:G.ColorIndex): Hush ((Phone G).coord i ∘ Y) r
structure Once (f g:E!→ℝ):Prop where
     sm : ContDiffAt ℝ ω f 0
     zero : Hush f 2
     sg : ContDiffAt ℝ ω g 0
abbrev ψPower (f g:E!→ℝ) (v:ℝ) (x:E!):= ((v^2:ℝ)⁻¹*v) • DColor b p f x + v • DColor b p g x
abbrev τPower(f g:E!→ℝ)(Y:E!→U!)(r:ℕ)(v:ℝ)(x:E!):=
     (v^r:ℝ)⁻¹ * (ψPower p b f g v x (Y x)) - ((v^r:ℝ)⁻¹*v) * duty (Phone G) (DColor b p Y x)
variable {p b S}{f g:Keys G I→ℝ}{Y:Keys G I→G.Color}{r:ℕ}
lemma T_B (z:E!)(V:ℝ)(h:ContDiffAt ℝ ω Y z):
     τPower p b f g Y r V z=∑ i:G.ColorIndex, let Q:= Phone G i
        let q:= (Phone G).coord i (Y z)
        (((V^2)⁻¹*V)* DColor b p f z Q+V*DColor b p g z Q)*((V^r)⁻¹*q)-((V^r)⁻¹*V)* DColor b p (((Phone G).coord i)∘Y) z Q:=by
       let A:= ψPower p b f g V z; let C:= DColor b p Y z; unfold τPower; nth_rw 1 [← (Phone G).sum_repr (Y z)]; rw [map_sum]; unfold duty; rw [mul_sum,mul_sum,←sum_sub_distrib]; apply sum_congr rfl; intro i _; rw [map_smul]; let T:= ((Phone G).coord i).toContinuousLinearMap; have ht(u): DColor b p (T∘Y) z u= (Phone G).coord i (C u):=by unfold DColor; rw [fderiv_comp z T.differentiableAt (h.differentiableAt (by simp)), T.fderiv];rfl
       dsimp only; erw [ht]; unfold ψPower; simp only [_root_.add_apply, _root_.smul_apply,smul_eq_mul]; change _ - _=((_ + _) * ((V^r)⁻¹ * ((Phone G).repr (Y z) i))) - ((V^r)⁻¹*V) * ((Phone G).coord i) (DColor b p Y z ((Phone G) i)); ring -- C mismatch
lemma Mixr (h:Variance.Cand r Y)(hf: Once f g)(x:ℝ→Keys G I)(hv:Gael x):
    Reads (fun t:ℝ=> τPower p b f g Y r t (t • x t)) (Mining (Cake p b f g Y r) x):=by
       let y(t:ℝ):= t • x t; let U:=B; let ζ:=Y; let Ψ(i:G.ColorIndex):=Topper p (U i) b; let V:= Pawn.mold f 2; let G':= Pawn.mold g 0; let u(i:G.ColorIndex):= (Phone G).coord i ∘ Y; let w(i):= Pawn.mold (u i) r; let W(i:G.ColorIndex):=LoopM p (U i) b V G' (w i); let rc(t:ℝ):=(t^r)⁻¹; let p0(i:G.ColorIndex)(t:ℝ):= (t^2)⁻¹*t*DColor b p f (y t) (U i); let p1(i:G.ColorIndex)(t:ℝ):=t*DColor b p g (y t) (U i); let F(i:G.ColorIndex)(v:ℝ):= (p0 i v+p1 i v)*(rc v*u i (y v))-(rc v*v)*DColor b p (u i) (y v) (U i)
       have hx(i:G.ColorIndex): W i= (Ψ i V+ Ψ i G')* w i+ -Ψ i (w i):=by unfold W LoopM Stamp;rw [plyAdd _ _ _ V G' (tallJ _ _) (tallJ _ _),sub_eq_add_neg]
       have he(i)(q:ScriptJ E!)(h:q.B):ScriptJ.B (Ψ i q):= fluxB (I:=G.ColorIndex) _ _ _ (fun _ _=>tallJ 0 _) _ h
       have hX(i):Reads (F i) (Mining (W i) x):=by
            rw [hx,miningAdd _ _ _ (height (ScriptJ.key (he i _ (tallJ _ _)) (he i _ (tallJ _ _))) (tallJ _ _)) (tauNeg _ (he i _ (tallJ _ _))) hv, MiningN _ _ (he _ _ (tallJ _ _)) hv, MiningM _ _ _ (ScriptJ.key (he _ _ (tallJ _ _)) (he _ _ (tallJ _ _))) (tallJ _ _) hv,miningAdd _ _ _ (he _ _ (tallJ _ _)) (he _ _ (tallJ _ _)) hv]
            have ht:= lanceM p b (U i) 0 g x hv hf.sg (fun _ _ h=>False.elim (Nat.not_lt_zero _ h)); simp only [pow_zero,inv_one,one_mul] at ht; have hh:ContDiffAt ℝ ω (u i) 0:= ((Phone G).coord i).toContinuousLinearMap.contDiff.contDiffAt.comp _ h.smooth
            exact (((lanceM p b (U i) 2 f x hv hf.sm hf.zero).sum ht).pile (Signal r _ hh (h.silent i) x hv)).minus (lanceM p b (U i) r _ x hv hh (h.silent i))
       apply (MiningU W univ F x hv (fun i _=> stampL _ _ _ (fun _ _=> tallJ _ _) _ _ (ScriptJ.key (tallJ _ _) (tallJ _ _)) (tallJ _ _)) (fun i _=>hX i)).cong
       have ht:Tendsto y μ (𝓝 0):=by unfold y; simpa using! (show Tendsto (fun i:ℝ=>i) μ (𝓝 0) from nhdsWithin_le_nhds).smul ((Gael.oath hv).limit)
       filter_upwards [ht.eventually (h.smooth.eventually (by simp))] with t ht; rw[Finset.sum_apply]; exact T_B (y t) _ ht
end YM.OPE.Variance

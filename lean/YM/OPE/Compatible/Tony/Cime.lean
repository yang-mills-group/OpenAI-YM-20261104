import YM.OPE.Compatible.Tony.Rue
/-! # Warrant.Ph reading.Port P with every epoch measure
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
namespace Sleeve
variable {I J:Type}{A:I→ Side}{a c:ℝ}{φ:Filter I}{Z:I→ℝ}{W:I→ℕ}
variable {p p' q q':GlyphQ G A}{V U:Forge G A}
lemma LiftD (s:Phase)(p q:Forge G A): LiftA s (p-q)=LiftA s p- LiftA s q:=by funext i x; change _* (p i x-q i x)= _*_-_*_; exact mul_sub ..
lemma Tok_diff (X Y:Forge G A)(s:Phase)(h:Silks φ Z a (X-Y)): Silks φ Z a (LiftA s X-LiftA s Y):= LiftD ..|>.subst (h.rise s)
namespace Scaffold
variable {B: Scaffold φ Z A W r}
variable (h: Shor B p p') (h':Shor B q q') (e:↥(fieldP r))(u:G.ColorIndex)
include h in private lemma lout (k:ℕ): Silks φ Z a (ofCourse (rerun e.val u p) k-ofCourse (rerun e.val u p') k):=by
        constructor; intro i; fin_cases i<;>first | exact ((h.rim e u k a).1) | exact ((h.rim e u (k+1) a).1) | exact ((h.rim e u (k+2) a).1)
-- separate for Shapes.Then sum
private lemma kite {p:GlyphQ G A}(hp:∀ i, ContDiffAt ℝ ω (p i) 0) : loft A e.val u (ofCourse p 2)= ofCourse (rerun e.val u p) 1:= funext fun i=>pry_mold (p i) 1 (hp i) _
private lemma kiteL {p:GlyphQ G A}(hp:∀ i, ContDiffAt ℝ ω (p i) 0) : loft A e.val u (ofCourse p 0)= LiftA 1 (ofCourse (rerun e.val u p) 0):=by funext i; rw [show loft A e.val u (ofCourse p 0) i=Pry _ (Pawn.mold (p i) 0) from rfl,pry_m0 (p i) (hp i)];funext x; change _* _= Ū^1*_;rw[pow_one];rfl
private lemma SumRoot (p q:GlyphQ G A):loft A e.val u (billcoat p q)=loft A e.val u (ofCourse p 2)+loft A e.val u (ofCourse q 0):=funext fun _=> Variance.pryAdd _ _ _ (tallJ _ _) (tallJ _ _)
private lemma rotor (X:Forge G A):Torque e.val u X=∑ i:G.ColorIndex,(fun (k:I)=>Mount (sett (A k) 0 e.val) (Phone G u) false i) * loft A e.val i X:=by funext i; rw[Finset.sum_apply];rfl
private lemma addR (p q:GlyphQ G A)(k:ℕ)(Y:CrysP A G): Flan e.val p q Y k=∑ i:G.ColorIndex, (Torque e.val i (billcoat p q)* ofCourse (N:=A) (G:=G) (fun j=> (Phone G).coord i ∘ Y j) k- Torque e.val i (ofCourse (N:=A) (G:=G) (fun j=>(Phone G).coord i ∘ Y j) k)):= by funext i;rw[Finset.sum_apply];rfl
include h h'
lemma novA : Silks φ Z a (Torque e.val u (billcoat p q)-Torque e.val u (billcoat p' q')):=by
        rw[rotor,rotor,← sum_sub_distrib]; apply Silks.sum B.top.fair; intro i _; rw[← mul_sub,mul_comm]; apply Silks.prod B.top.fair; swap;· exact paid B.top (hold_stamp B.top e u i)
        rw [SumRoot,SumRoot,kite (e:=e) i h.smooth_f,kite (e:=e) i h.smooth_s,kiteL (e:=e) i h'.smooth_f,kiteL (e:=e) i h'.smooth_s] 
        let X:= ofCourse (rerun e.val i p) 1; let x' :=ofCourse (rerun e.val i p') 1; let Y:=LiftA 1 (ofCourse (rerun e.val i q) 0); let y':=LiftA 1 (ofCourse (rerun e.val i q') 0); change Silks _ _ _ (X+Y-(x'+y')); rw[show X+Y-(x'+y')=X-x'+ (Y-y') by abel]; exact Silks.green B.top.fair (lout h ..) (Tok_diff _ _ _ (lout h' ..)) -- dot..
lemma HarvestT (X:CrysP A G)(hx:ShineX B.top X k e): Silks φ Z a (Flan e.val p q X k-Flan e.val p' q' X k):=by
        rw [addR,addR,← sum_sub_distrib]; apply Silks.sum B.top.fair; intro i _; rw [sub_sub_sub_cancel_right,← sub_mul]; exact (novA h h' _ i).prod B.top.fair (paid B.top (hx.cost i))
omit h h'
variable {K:Sponsor G}{T:Seasons K}{v:I→ℝ}(Y:(j:I)→ Alps K T i (v j))
lemma gleams (hp:Shor B (HabitK A Y) p)(ht:Shor B (HabitL A Y) q)(hv:WageK B.top Y p q V U): Silks φ Z a (V-U):=by
        induction hv with
        | empty=> rw [sub_zero]; exact Silks.empty
        | piece X l e s h=>exact Tok_diff _ _ _ (HarvestT hp ht e X h)
        | @cong x y z t h hv ih=> exact ih.doyen (hv.mono fun i hi=> congr_arg₂ (·-·) hi.1 hi.2)
        | @add x y z t h he H ht=> rw [show x+z-(y+t)=x-y+(z-t) from by abel]; exact Silks.green B.top.fair H ht
end Scaffold
end Sleeve
end YM.OPE.Merchant

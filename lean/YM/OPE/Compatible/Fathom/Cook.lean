import YM.OPE.Compatible.Fathom.Ravine
import YM.OPE.Compatible.Bust.Frag
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
open Silt.Float Silt Cloud
open Finset
section w
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
open Adhesion
lemma jetLyr (f:E→ℝ)(n:ℕ):anthem n (Radial.jet f n):= (lyricCost (iteratedFDeriv ℝ n f 0)).scale _
lemma corsage (f w:E→ℝ): Carat (Curling f w):=by
       let u:=Pawn.mold f 2; let p:=Pawn.mold w 0; apply skS (q:=fun _:E=> JetS.plainJ (w 0)⁻¹) (s:= p * (wheel u)) (fun _=> ArtBank _)
       apply skS (fun j=>?_)
       · intro i; let K:E→ℝ:= Radial.jet f 3; let T:=Radial.jet f 4; have hp(n:ℕ)(l:E→ℝ) (hh: anthem n l):anthem n (-l):=(by simpa using hh.scale (-1)); fin_cases i
         · exact anthem.bank _ _
         · exact hp _ _ (jetLyr f 3)
         change anthem 6 (fun i=> -T i+(K i)^2/2); have hh:= ((hp _ _ (jetLyr f 4)).bloat (by omega:4 ≤ 6)).add (q (K:=K) (jetLyr f 3)); exact hh
       fin_cases j; exact jetLyr w 0; exact (jetLyr w 1).bloat (by simp); exact (jetLyr w 2).bloat (by simp)
where q {K:E→ℝ}(h:anthem 3 K):anthem 6 (fun i=> (K i)^2/2) :=by rw[show (fun i=> (K i)^2/2)=(2:ℝ)⁻¹ • K^2 from funext fun i=>by simp;ring]; exact (h.powers 2).scale _
variable [MeasurableSpace E][BorelSpace E][Fintype I]
omit [BorelSpace E] in lemma atlasH (F:Fiber E G I)(P:ChartRatio G): Carat (F.cloth P):=fun j=> ((corsage F.f (F.wSign P)) j).compLinear (Fiber.drape _ _ F.M).toLinearMap
variable (μ:Measure E)[μ.IsAddHaarMeasure]
lemma visionG (V:Fiber E G I)(P:ChartRatio G)(h:LocalRatio P)(B:Law E)(q:E×Keys G I→Token)(hz: MoldH (united B V.Q) (μ.prod (Chart.tangent G I)) j (q ∘ Fiber.drape E _ V.M)): MoldH B μ j (V.predicts P q) := wrappedT hz (atlasH V P) fun _=> curT (V.signPay h) _
end w
end YM.OPE.Cascade.Paver

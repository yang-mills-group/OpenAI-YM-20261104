import YM.OPE.Compatible.Anchor.Trust
/-! # valuation calculus and instruments -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r n l s:ℕ}{Z I J M E F:Type}
-- no Ω.Parameters.
local notation "θ"=> 𝓝[>] (0:ℝ)
abbrev BillUp (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](k:ℕ)(u:ℝ→E)(v:E) := Tendsto (fun t:ℝ=>(t^k)⁻¹ • u t) θ (𝓝 v)
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] {p:E}{s:ℕ}{f:ℝ→E}
lemma UpPure (p:E): BillUp E d (fun x:ℝ=> x^d • p) p :=by apply tendsto_const_nhds.congr'; filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with k hk; have hk:0 < k:= hk; rw [inv_smul_smul₀ (by positivity)]
lemma UpLayer (S:Finset I)(f:I→ℝ→E)(p:I→E)(h:∀ i∈S,BillUp E d (f i) (p i)): BillUp E d (fun x=> ∑ i∈S,f i x) (∑ i∈S,p i):=by unfold BillUp; simp_rw [Finset.smul_sum]; exact tendsto_finsetSum S h
lemma UpPrice (p:E)(hf:k≤d): BillUp E k (fun t:ℝ=>t^d • p) (if k=d then p else 0):=by
     split
     next h=>subst k; exact UpPure _
     next h=> exact WardBin.falls (lt_of_le_of_ne hf h) (UpPure p)
lemma Up_h (h:BillUp E d f p)(L:E→L[ℝ] F): BillUp F d (fun t=>L (f t)) (L p):=by unfold BillUp; simp_rw [←map_smul]; exact L.continuous.continuousAt.tendsto.comp h
end
variable {K:Sponsor G}{T:Seasons K}{v:ℝ}
local notation "C!"=> fieldX (Shade G)
noncomputable abbrev wageZ (A:Alps K T i v)(m:Fin j→Axis)(x:C!)(a:Axis)(y:Cover):= trainX G.Color j m (fun w=> rootζ A x (w,a)) y
lemma pinsZ (A:Alps K T i v)(m:Fin j→Axis)(x:C!)(a:Axis)(y:Cover)(i:G.ColorIndex): wageZ A m x a y i= roamsX m (meetsX (barrage (pink K.K.penalty A.gear)) (shadew i x)) (y,coord a):=by
     let p(w:Cover):=rootζ A x (w,a); let u:= (Phone G).coord i; rw [← phone_eq]; change (u ∘ (trainX G.Color j m p)) y= _; rw [← tracksX,roams_eq]; apply congr_fun (f:=trainX ℝ j m (u ∘p)); congr 1
lemma ΩCapital (A:Alps K T i v)(hp:4 ≤ i)(p:Fin j→Axis)(a:Axis)(x:Taylor G (j+1))(w:Cover):
     wageZ A p (jetΦ G _ x) a w= - ((j+1).factorial:ℝ) • flame x a (basis ∘ p):=by
          ext k; rw [pinsZ]; exact candle _ ((heart_saves K.K.penalty K.K.penalty_pos hp (fun i:Train i=>i)).1.whole _) (Flume.Script.dew hp K.K _) x p w a k|>.trans (by change -((_ :ℝ)*_) = - (_:ℝ) * _; ring_nf; rfl)
lemma BlankΩ (A:Alps K T i v)(hp:4 ≤ i)(p:Fin j→Axis)(a:Axis)(x:Taylor G d)(w:Cover)(h:d<j+1): wageZ A p (jetΦ G d x) a w=0:=by ext k; rw [pinsZ]; exact candleLow _ ((heart_saves K.K.penalty K.K.penalty_pos hp (fun i:Train i=>i)).1.whole _) (ledgeL x.val) (Nat.add_lt_add_right h 1) _ .. -- elabor
end YM.OPE.Variance

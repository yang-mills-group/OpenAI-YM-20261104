import YM.OPE.Compatible.Zephyr.Shine
import YM.OPE.Compatible.Porch.Citro
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Articles
/-!
# Exact localized pieces; radial estimator from mixed purchases. Blueprint
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Zeph
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Matrix Bloch Precision Exterior Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra GaussianScore Metric Push Push.AbsoluteSums
variable {G:Gauge}{c f:Side}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate
open Woody Next.Free
variable {N:ChartRatio G}{t r R B b:ℝ}
variable (S:StepData c f) (F: Forest S.ratio)
local notation "Q" =>(Bid.Dir G c × AxisChart G F)
noncomputable abbrev PinW (G:Gauge) := (Stationary.arm G f 1).toContinuousLinearMap ∘L (Stationary.pad F ∘L ContinuousLinearMap.snd ℝ (Bid.Dir G c) (AxisChart G F))
lemma pinShape (e:Edge (Site f))(x:Q) : PinW S F G x (e.1,coord e.2)=(if h:e∈F.trunks then 0 else x.2 ⟨e,h⟩):=by
   change Stationary.edgeColor _ _=_; split
   next h=> exact Stationary.pad_trunk F x.2 ⟨e,h⟩
   next h=> exact Stationary.pad_free F x.2 ⟨e,h⟩
lemma pinUnit (x:Q): ‖PinW S F G x‖≤‖x‖:=by
   apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2; rintro ⟨i,j⟩; obtain ⟨p,rfl⟩:= axisEquiv.surjective j; rw [show PinW S F _ x (i,axisEquiv p)=_ from pinShape S F (i,p) x]; split; rw [norm_zero]; exact norm_nonneg _; exact (norm_le_pi_norm _ _).trans (le_max_right ..)
lemma LightOn (x:Q)(i:Site f)(he:On S F G t i x b)(hh:0≤b): trials G t i (PinW S F G x) b:=by
    rintro ⟨l,k⟩; obtain ⟨p,rfl⟩:= axisEquiv.surjective k; rw [show PinW S F _ x (l,axisEquiv p)=_ from pinShape S F (l,p) x]; split
    · rw [norm_zero]; exact mul_nonneg hh (Progress.StationaryScenes.Green.wt_pos ..).le
    next h=> exact he.2 ⟨(l,p),h⟩
lemma Pines (x:Q): represent (PinW S F G x)=fieldF F x.2:=by rw [spoolP F]; rfl
namespace Dew
-- costs max0. Seed/GLOBAL with TOP.SEC.
structure Pile (r a t:ℝ)(m:ℕ)(Y:Q→ℝ)(p:Site f→ Q→ℝ):Prop where
       pays {x:Q}: ‖x‖<r → Y x=∑ i,p i x
       meter (j:Site f) (x:Q): ‖x‖<r → ContDiffAt ℝ ω (p j) x
       voice (j:Site f)(x:Q): ‖x‖<r → ∀ i, i ≤ m → Costs (On S F G t j) (Radius.Polish.budget ℝ) (p j) x i a
variable (P:Clip)(A:PathData G){s f1 v:ℝ}{d:ℕ}
open Progress.StationaryScenes AnalyticNext.QuarticMatch.Local
lemma got (h:A.Bounds P s f1 v):
    Pile S F 1 (dues G s f1 P d) (down s d) d (fun x:Q=> mainTerm P A (fieldF F x.2)) (fun j=> Rotate.byStage P A j ∘ PinW S F G) ∧
    Pile S F 1 (Real.exp (2* down s d)^d*nearCost G d s v) (down s d) d (fun x:Q=> springF F A x.2) (fun j=> byLoop A j ∘ PinW S F G):=by
       have he {x:Q}{i t}(p:Bid.Dir G f→ℝ)(s b:ℝ)(j:Site f)(hp:Costs (trials G t j) (Radius.Polish.budget ℝ) p (PinW S F G x) i b)(hz:ContDiffAt ℝ ω p (PinW S F G x)): Costs (On S F G t j) (Radius.Polish.budget ℝ) (p ∘ PinW S F G) x i b:=by
             intro u c hh; rw [lin_rate_at p _ _ hz]; exact hp _ c (fun i=> ⟨(hh i).1, LightOn S F (u i) j (hh i).2 (hh i).1⟩)
       refine ⟨⟨fun {x} _=> ?_,fun j x _=> (Rotate.stage_rate h j (PinW S F G x)).comp x (PinW S F G).contDiff.contDiffAt,fun j x hz i hi=>he _ s _ _ (first h _ hi _ ((pinUnit S F x).trans_lt hz) _) (Rotate.stage_rate h j _)⟩,⟨fun {x} _=>?_,fun j x _=>(key_rate h j (PinW S F G x)).comp x (PinW S F G).contDiff.contDiffAt,fun j x hz i hi=>he _ s _ _ (nextLoop h _ hi _ ((pinUnit S F x).trans_lt hz) _) (key_rate h j _)⟩⟩
       · rw [←Pines S F x]; exact Rotate.unroll P A _
       unfold springF; rw [← Pines S F x]; exact byKey A _
end Dew
end YM.OPE.Zeph

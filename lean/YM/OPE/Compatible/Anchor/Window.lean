import YM.OPE.Compatible.Anchor.Glen
/-! # cylinder templates for R transport in force Ward. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J M E F:Type}{n:Side}
local notation "Y!" => Bid.Dir G n
local notation "Q!"=>CoverConfig G
structure Sensed [NormedAddCommGroup F][NormedSpace ℝ F](f:CoverConfig G → F):Prop where
     see: Realm f
     sense(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (u:E→CoverConfig G): (∀ i:RootEdge,ContDiff ℝ ω (fun p=>G.mat (u p i)))→ContDiff ℝ ω (f ∘ u)
lemma railLeg (d:Step)(x:Cover): Sensed (fun v:Q!=> G.mat (d.read v x)):=by
     refine ⟨⟨{d.used x},fun u v h=>?_⟩,fun E _ _ y H=>?_⟩; unfold Step.read; dsimp only; rw [h (show d.used x∈ ({d.used x}:Finset _) from Finset.mem_singleton_self _)];
     unfold Function.comp Step.read; cases h:d.neg
     · simpa only[Bool.false_eq_true,if_false] using H _
     simp only[↓reduceIte,G.mat_inv]; exact (starL ℝ (A:=G.Mat)).contDiff.comp (H _)
lemma candleTravel (x:Cover)(w:Walk): Sensed (fun v:Q! => G.mat (travel v x w)):=by
     induction w generalizing x with
     | nil=> exact ⟨⟨∅,fun _ _ _=>rfl⟩,fun _ _ _ _ _=>contDiff_const⟩
     | cons d w ih=>
       let v (p:Q!):= G.mat (d.read p x); let u(y:Q!):= G.mat (travel y (x+d.vec) w); rw [show (fun p:Q! => G.mat (travel p x (d::w)))=v*u from funext fun y=> G.mat_mul ..]; have hp:Sensed v:=railLeg ..; have h:= ih (x+d.vec); refine ⟨?_,fun E _ _ g H=> (hp.sense E g H).mul (h.sense E g H)⟩; obtain ⟨s,hs⟩:=h.see; obtain ⟨t,ht⟩:=hp.see; exact ⟨t∪s,fun g f h=>congr_arg₂ (·*·) (ht _ _ (h.mono fun _ hl=>Finset.mem_union_left _ hl)) (hs _ _ (h.mono fun _ hl=>Finset.mem_union_right _ hl))⟩
-- template Sensor. space proof
lemma boardSeen (i:Cover×Shade G): Sensed (fun x:Q!=> board x i):=by
      let a:= i.2.2; let P:Q!→G.El:=fun x=>travel x 0 (ringO (i.1,i.2.1)); let L:= (pleatsF a).toContinuousLinearMap; have he:Sensed (G.mat ∘ P):= candleTravel ..; rw [show (fun x:Q!=> board x i)=(fun x:G.Mat=>L (x-1))∘(G.mat ∘ P) from funext fun v=> (pleatsEq ..).symm]; refine ⟨realmMap he.see _,fun E _ _ p hp=> ?_⟩; exact (L.contDiff.comp (contDiff_id.sub contDiff_const)).comp (he.sense E p hp)
section any
variable {Y:I→ Type}[Fintype I][∀ i, NormedAddCommGroup (Y i)][∀ i, NormedSpace ℝ (Y i)]
lemma candles (p:∀ i:I,Q!→Y i)(h:∀ i,Sensed (p i)): Sensed (fun v:Q!=>fun i=>p i v):= by refine ⟨?_,fun E _ _ v H=> contDiff_pi.mpr fun i=>(h i).sense E v H⟩; exact realms (X:=fun v:Q!=>fun i=>p i v) (f:=fun (i:I) (y:∀ j,Y j)=>y i) (fun j=> (show Realm _ from (h j).see))
end any
variable [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup E][NormedSpace ℝ E]
lemma Sensed.chain {p:Q!→E}(h:Sensed p)(k:E→F)(hp:ContDiff ℝ ω k):Sensed (k∘p):=⟨realmMap h.see k,fun F _ _ u h'=>hp.comp (h.sense F u h')⟩
end YM.OPE.Variance

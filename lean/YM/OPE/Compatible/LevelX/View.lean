import YM.OPE.Compatible.LevelX.Rank
/-! # Grade taps. lifts and kernels -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
section
variable (h:e-r≤m)
local notation "B!"=> bed G k m
local notation "J!"=> partX G r (e-r) d
local notation "A!"=> Alphabet G d
local notation "F!"=>coordinateQ G d e r
-- compute finite rank with test axes.All.Topo.
lemma ambience (x:Fin r→Alphabet G d):Continuous (fun p:bed G k m=>(Flume.Script.tiller G r m (e-r) h d (terrace G k m r p)).val x):=by
      let E(w: B!):= terrace G k m r w; let q(w:B!):=Flume.Script.tiller G r m (e-r) h d (E w); change Continuous (fun b=>(q b).val x); rw [funext (show ∀ w:B!, (q w).val x= _ from fun i=> deckSum (q i).val x)]; apply continuous_finsetSum _ fun i _=>?_ ; let y(j):= monoX (i j) (x j (i j)); have he(i:B!) : (q i).val=honeyX (E i).val (patent_till _) h d:=rfl
      let t (j:B!) := (E j).val; let f(w:B!):= (q w).val y; change Continuous f; by_cases ht: rankX i=e-r
      · rw [show f= _ from (show f=fun b:B! => wholeX (t b) (fun j=> ledge (x j (i j)).val) from funext fun b=>(solid_mono (t b) (patent_till (E b)) h i _).trans (if_pos ht))]; exact whiff _ _ (fun j: Fin r=> low_quiet (ledgeL (x j (i j)).val)) (ht.trans_le h)
      rw [show f= fun _=>0 from funext fun z=>(show Off G r (e-r) d (q z).val from (q z).property).Grades i (fun j=> x j (i j)) ht]; exact continuous_const
set_option maxHeartbeats 200000 in
lemma alumni (G:Gauge)(k d e r m:ℕ)(h:e-r≤m):Continuous (grasps G d e k m r h):=by
      let B:=finBasis ℝ (Alphabet G d); let C:=(TagW G d e r); let T:= coordinateQ G d e r; let p(t:C)(a: Fin r→ Fin (finrank ℝ (Alphabet G d))):=(T.symm t).val (B∘a) -- bug name
      let X:=Fin r→ Fin (finrank ℝ (Alphabet G d)); let L:C→ₗ[ℝ] PAD X:={ toFun:=p,map_add' i j:=by ext1 a; unfold p;rw [map_add];rfl, map_smul' i j:=by ext1 a; unfold p; rw [map_smul]; rfl }
      have hp: Injective L:=by
           intro v w hv
           apply T.symm.injective
           apply Subtype.ext
           apply Module.Basis.ext_multilinear (fun _ : Fin r => B)
           intro i
           exact congrFun hv i
      let V:= L.leftInverse; let f:=grasps G d e k m r h; have hg:Continuous (fun p:bed G k m=> L (f p)):=continuous_pi fun i=>by
           let y:= B ∘ i; let u(b:bed G k m):=Flume.Script.tiller G r m (e-r) h d (terrace G k m r b); change Continuous (fun b=>(T.symm (T (u b))).val y); simp_rw [LinearEquiv.symm_apply_apply]; exact ambience h y
      rw [show (⇑f:bed G k m→TagW G d e r)=V ∘ L ∘ f from funext fun i=> (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hp) ..).symm]; exact V.continuous_of_finiteDimensional.comp hg
end
end YM.OPE.Drift

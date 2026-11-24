import YM.MS.Alps.Ropes
import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Odelta
/-!
# D-time derivatives at arbitrary finite scale of actual generator

Use polar tester only for the Γ-free ocean operation. Simpler speed on all finite
 RHS terms at horizon with finite sum. Action linear; flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff Interval
variable {E F I: Type} {G:Gauge}{b c:Bool}{p t:ℝ}
variable {u v:ℝ→ Mob G}{r:ℝ→ Rip G}{H Y: Mob G}{V:Rip G}
lemma speed_port (h:speed u H t)(Q: Shade G): speed (fun t=>portZ Q (u t)) (portZ Q H) t:= fun i l=> ZQ _ (h i) l
lemma speed_arbor (h:speed u H t)(he:speed v Y t)(hr:speedR r V t)(hk:∀ i,reverseF (r i))(hV:reverseF V):
   speed (fun i=>arbor (r i) (u i) (v i)) (arbor V (u t) (v t)+arbor (r t) H (v t)+arbor (r t) (u t) Y) t:=fun i l=> tree_zip (fun j=> hk j i) (hV i) (hr i) (h i) (he i) l -- shift syntax
lemma Curve.heard (h:Curve u H t)(hr:BeamR r V t)(hf:∀ t, Form0 b (u t))(he:Form0 b H)(hU:∀ t, Knot b (r t))(hv: Knot b V){z:ℂ}(hq:z∈Town): Curve (fun i=> ocean z (r i) (u i)) (ocean z V (u t) + ocean z (r t) H) t := by
    let U (x:Trail0 t):= r x-r t; let Q (x:Trail0 t):= u x-u t; let X:=polar u H t; let Y:= beamR r V t; have hP (i:Trail0 t): polar (fun i:ℝ=> ocean z (r i) (u i)) (ocean z V (u t) + ocean z (r t) H) t i = ocean z (U i) (Q i) + ocean z (r t) (X i) + ocean z (Y i) (u t) := by
        unfold X Y polar beamR U Q; dsimp only; rw [oceanLsub (hU _) ((hf _).sub (hf _)) (hU t) hq, oceanRsub (hU _) (hf _) (hf t) hq, oceanRsub (hU t) (hf _) (hf t) hq, oceanRsub (hU t) ((hf _).sub (hf _)) (he.smul _) hq, oceanRsub (hU _) (hf _) (hf _) hq, oceanLsub ((hU _).sub (hU t)) (hf _) (hv.smul _) hq, oceanLsub (hU _) (hf _) (hU _) hq, scaleR (hU _) he,scaleL hv (hf _),smul_add]; abel
    obtain ⟨n,hn⟩:= exists_nat_ge (2*z.re+1); have hℓ {a b':Trail0 t→ℝ}{F:Trail0 t→Mob G}{R:Trail0 t→Rip G}(hT:fell 0 a F)(hR:rib 0 b' R)(h:∀ i,Sturdy b (F i))(hp:∀ i,Ruddy b (R i))(hq':∀ i,0≤b' i) := regular_fin (fun i:ℕ=>const_sc (z:=(0:UScale (Trail0 t))) ‖2*(z-i)‖) hT hR (fun _=> hq) (fun _=>hn) h hp hq' -- hℓ type inferred z? check
    refine ⟨?_⟩; rw [funext hP]; refine fall_add (fall_add ?_ ?_) ?_
    · convert! hℓ (curve_v h he.price) (knot_v hr hv.price) (fun i=>((hf _).sub (hf _)).token) (fun i=>((hU _).sub (hU _)).token) (nn0 t) using 1; ext x; rw [between,pow_two]
    · convert! hℓ h.pay (transport (hU t).price) (fun i=>(((hf _).sub (hf _)).sub (he.smul _)).token) (fun _=> (hU t).token) (fun _=> zero_le_one) using 1; simp
    convert! hℓ (travel (hf t).price) hr.pay (fun i=>(hf t).token) (fun i=>(((hU _).sub (hU _)).sub (hv.smul _)).token) (flag_nn t) using 1; simp
lemma speed_add (h:speed u H t)(hv:speed v Y t): speed (u+v) (H+Y) t:= fun m l=> (h m l).add (hv ..)
lemma speed_sum (J:Finset I){F:I→ℝ→Mob G}{U:I→Mob G}(h:∀ n∈J,speed (F n) (U n) t): speed (fun i=>∑ j∈J,F j i) (∑ j∈J,U j) t:= by intro m l; simp_rw [Finset.sum_apply]; apply HasDerivAt.fun_sum; exact fun i hi=> h i hi m l
lemma speed_mul (h:speed u H t)(c:ℂ): speed (c • u) (c • H) t:= fun m i=> (h m i).const_mul _
end YM.MS.Alps

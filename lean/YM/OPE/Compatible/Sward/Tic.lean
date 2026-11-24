import YM.OPE.Compatible.Sward.Oak
import YM.OPE.Compatible.Frog.Eye
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
open Votive
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
open PertExtension Series GaussianScore
open Matrix
section
lemma levelT (p:Tower (Shade H) d τ)(u:Phase): skry (inkM (spread H d τ p) d x) u=LightP x (m:=τ u) (p u):=funext fun _=> vein_i ..
lemma sweet (W:Aware d τ)(p:Tracts H d τ)(A:RowB (Shade H)):
     Rainbow (spread H d τ (FoldV W p A)):=by
         let g(j:Char.Phase):= Raft p A j; have he(j:Char.Phase):Rainbow (spread H d τ (scrollF H W j (g j))):=by
              rw [splitF]; let n:=d+j.val+1; let U(i: Fin n):=Drift.glide (Grid.lance ((lilies (τ j) (d+j.val) _ (g j).val) i.val)) j; have hv(t:Finset (Fin n)): Rainbow (∑ i∈t,U i):=by
                   induction t using Finset.induction_on with
                   | empty=>rw[sum_empty]; exact fun _ _ _=>rfl
                   | insert i x hx ih=> rw[sum_insert hx]; exact bright (lancing _ _) ih
              exact hv univ
         let S:= spread H d τ; have hz(t: Finset Char.Phase):Rainbow (∑ i∈t, S (scrollF H W i (g i))):=by induction t using Finset.induction_on with| empty=> rw[sum_empty]; exact fun _ _ _=>rfl | insert i sL h ih=> rw [sum_insert h]; exact bright (he i) ih
         rw[FoldV,map_sum]; exact hz _ -- need lancing
-- SELF step
variable {P:Sponsor H} (v:Train r) (h:4 ≤ r)
lemma vessel_c :Licence (flats H N).toContinuousLinearMap (Vessel L v H N h) v L:=by
       intro x y hx _; rw [show chamber _ _=_ from (Hport L v H N h).choose_spec.1]; exact (blankV v h x hx y).symm
abbrev TrueRay (p: Tower (Shade H) d τ) (k:ℕ):Prop:=∀ u:Phase, Deep (m:=τ u) (boostS (atlasF H v h L) (1/2) (τ u) (d+u.val) (p u)) (k+3*(2-u.val))
-- sturdy
variable (W:Aware d τ)
lemma OrbitS (p: Tracts H d τ)(hp:ratios p k): TrueRay (L:=P.K) v h (Fallix H W P v h p).val k:=by
       intro z; let T:=FoldV W p (atlasF H v h P.K); have hs:T=(Fallix H W P v h p).val:=chartX W p v h; rw [←hs]; apply kuff _ (turfy _ _ _ ((sweet W p _) z)) (b:=fun _=>d+z.val) ?_
       intro c; let u(i:ℕ):Side := ⟨c.val*(i+1),mul_pos c.pos (by omega)⟩; let Q:= d+z.val; let S(i):= FoldV W p (pointAt H v h P.K (u i)); have hu(i:ℕ):i+1≤(u i).val:= Nat.le_mul_of_pos_left _ c.pos; have hL:Tendsto (fun i=>(u i).val) atTop atTop:=tendsto_atTop_mono hu (tendsto_add_atTop_nat 1); have hv:Tendsto S atTop (𝓝 T):= tideF W p _ _ _ (farN H u v h P.K hL); refine lucid (m:=τ z) P.K v h (fun i:ℕ=> S i z) (T z) u (fun _=>0) (fun i=> dvd_mul_right ..) atTop hL tendsto_const_nhds ((tendsto_pi_nhds.mp hv z)) (n₀:=0) ?_ -- b
       refine Eventually.of_forall ?_; intro i; let t:=u i; let f:= flats H (u i); let R:= inkM (spread H d τ (S i)) d (0:Site (u i)); let B:= Vessel P.K v H t h; let Ω := Chart.tangent H (Exterior.Body 1 t); have hh:= glossB (0:Site (u i)) W p f.toContinuousLinearMap Ω B v h P.K (vessel_c v h) hp; have ht:MoldH B Ω k R:=by
             convert! hh using 1; ext1 w; exact (congr_arg R (f.symm_apply_apply w).symm)
       refine ⟨show settled (m:=τ z) (S i z) from (sweet W p _) z, le_rfl, skry R z, ht z, ?_, fun x=>?_⟩
       · rw[show skry R z=_ from levelT _ (S i) z]; exact polW ..
       rw [show skry R z=_ from levelT _ (S i) z]; simp
end
end YM.OPE.Silt.Phere

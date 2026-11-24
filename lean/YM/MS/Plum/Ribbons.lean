import YM.MS.Plum.Guard
/-!
# Rope approximations of Knot lines by compact for analytical identities

Sup Ray scale q≤2/c, uniform across n. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plum
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans
open Momentum Metric
open scoped Topology ContDiff
variable {I J E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 {G:Gauge}{z: UScale I} {v:I→ℝ}{U: Rip G}{m n:ℕ}{K:Shade G}

private def cap : ContDiffBump (0:ℝ):= ⟨1,2,zero_lt_one,by norm_num⟩
def fruit (p:SectorP m):ℂ:= ( cap p.sq:ℝ)
def twine (v:ℝ)(U: Rip G): Rip G:= fun n i j p=> fruit (v • p)*U n i j p
lemma fruit_even (p:SectorP m): fruit (-p)=fruit p:= by rw [fruit,Landau.sq_neg]; rfl
lemma grew (k:ℝ) {c:Bool} (h:Ruddy c U) : Ruddy c (twine k U) where
    grows hi p q x:= by rw [twine,twine,h.grows hi p q x, ← map_smul, fruit, sq_up,fruit]
    turn n X he p a b:= by
       unfold twine; rw [h.turn n X he p]; have hp : fruit (k • (flagS X G).volp p)=fruit (k • p):= by change fruit (k • X.turn p)=_; rw [← map_smul, fruit,X.fare,fruit]
       simp_rw [hp, Finset.mul_sum,mul_assoc]
-- difference estimates
private lemma food (m:ℕ): HasTemperateGrowth (fruit (m:=m)):= by
    refine Complex.ofRealCLM.hasTemperateGrowth.comp ( cap.hasCompactSupport.hasTemperateGrowth cap.contDiff|>.comp ?_); unfold Momentum.sq; exact HasTemperateGrowth.sum (fun i _=> (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Arts.L m=>ℝ) i).hasTemperateGrowth.pow 2)
private lemma small (m:ℕ): fruit (m:=m) 0=1:= by rw [fruit,show cap _=1 from ContDiffBump.one_of_mem_closedBall cap ?_]; simp; simp [Momentum.sq,cap]
lemma clip (p:SectorP m) (c:ℝ)(hc:0<c)(he: 2/c< ‖p‖): fruit (c • p)=0:= by
   have ht:= Momentum.sup_square (c • p); have hQ: (2:ℝ)< ‖(c • p)‖:=by rw [norm_smul_of_nonneg hc.le]; rw [mul_comm]; exact (div_lt_iff₀ hc).mp he
   unfold fruit; rw [show cap _=0 from ContDiffBump.zero_of_le_dist cap ?_]; · simp
   rw [dist_zero_right,Real.norm_of_nonneg (Momentum.sq_nonnegative _)]; exact (by change (2:ℝ) ≤ _; nlinarith [sq_nonneg (‖c • p‖-2)])
lemma ribbon (hv:∀ i,0<v i)(hH:∀ i,v i≤1)(H:rPrice U) : rib z v (fun i=>twine (v i) U - U):= by
   intro n a b; have ht := booty (z:=z) hv hH ((food n).sub (HasTemperateGrowth.const (1:ℂ))) (show (fun i:SectorP n=> fruit i - 1) 0=0 by simp [small]); convert! rails_mul (u:=fun i p=> U n a b p) (arced (H n a b)) ht using 1; ext i p; simp only [twine,Pi.sub_apply]; ring; simp
lemma wide (U:Rip G){p:ℝ}(h:0<p): rock (2/p) (twine p U):= fun i j k x ht=>by simp [twine, clip x p h ht]
lemma utility {p:ℝ}(h:0<p)(hv:p≤1)(H:rPrice U): rPrice (twine p U):= by
   obtain he:= ribbon (z:=(0:UScale Unit)) (v:=fun _=>p) (fun _=>h) (fun _=>hv) H;
   refine fun i a b n=>?_ ; have hz := he i a b n; convert! Costs.add ( hz.raise ?_) (H i a b n) using 1; · simp
   refine Cost.of_le fun _ q h=>?_ ; gcongr; exact pow_nonneg ((Arc.path 0).weight_pos _ _).le _ -- goal unwrap
lemma tried {c:Bool}(h:Knot c U)(n:ℝ)(hn:0<n)(hp:n≤1): RockB (twine n U) c:= ⟨⟨utility hn hp h.price,grew n h.token⟩,2/n,(by rw [le_div_iff₀ hn]; linarith), wide U hn⟩ -- Record nesting? earlier RockB constructor Gear Prop ∃ . syntax
end YM.MS.Plum

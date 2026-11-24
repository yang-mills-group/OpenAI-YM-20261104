import YM.GradedFar.Actual
import YM.Spec.Closed
/-!
# Index quantifiers for authentic `numeric` calls in the continuum comparison

This assertion retains the paired tails of `f#`: `forall^∞ p=f.per ..., forall^∞ N→∞`.
Hence not letting a few test families push the mesh stops to smaller p. Always every whole
address can run on these (fixed) compacts. Does not exclude the generic-axis ties.
Upstream `FullVolume.FixedBounds`, `FullVolume.PositionsUV` are separate hypotheses. Not claiming an
election. Exercise with same `Spec.Final`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Spec
open FullVolume
open Metric
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}(F:Final C f S)
    {n p :ℕ}
local notation "K*"=> generic n
lemma pulses {T K : Set (Points n)} (hK:IsCompact K)(hv:K⊆ interior T)(δ:ℝ)(hd:0<δ): ∃ A:Finset ↥(K*∩ T), K ⊆ ⋃ i∈ A, Metric.ball i.val δ := by
 refine hK.elim_finite_subcover (fun i: ↥(K*∩T)=>Metric.ball i.val δ) (fun _=> Metric.isOpen_ball) (fun x hx=>?_)
 have h:Dense K*:= Measure.dense_of_ae (almostGeneric n)
 obtain ⟨y,hy,hT⟩:= h.inter_open_nonempty (interior T∩Metric.ball x δ) (isOpen_interior.inter Metric.isOpen_ball) ⟨x,hv hx, Metric.mem_ball_self hd⟩
 exact mem_iUnion.mpr ⟨ ⟨y,hT,interior_subset hy.1⟩, Metric.mem_ball_comm.mp hy.2⟩

variable (hF:FixedBounds C)
include F hF
lemma many {w:Fin n→ C.book.Token} {L:ℕ→Points n→ℂ}(h:∀ p,Cluster C Extraction.Sequence.full p n (fun N=>lifted C N p w) (L p))
    {K:Set (Points n)}(hK:IsCompact K)(hV:K⊆conf n)(ε:ℝ)(he:0<ε): ∀ᶠ i in atTop,∀ x∈K,dist (L (f.per i) x) (S.read x w) ≤ ε:=by
 let X:=fun x=> S.read x w; let δ:=ε/4; have he':0<δ:=by dsimp only [δ]; positivity
 obtain ⟨T,hT,hv,hx⟩:= exists_compact_between hK (conf_open n) hV
 obtain ⟨d,b,hd,hb,H⟩:= lips hF h hT hx; have hc: UniformContinuousOn X T:= hT.uniformContinuousOn_of_continuous ((S.smooth_read F.room.kernel.smooth w).continuousOn.mono hx)
 obtain ⟨r,hr,hR⟩:= Metric.uniformContinuousOn_iff.mp hc δ he'; let t:=min (min d r) (δ/(1+b)); have ht:0<t:=lt_min (lt_min hd hr) (by positivity)
 obtain ⟨A,hA⟩:= pulses hK hv t ht; obtain ⟨P,hP,hL⟩:= F.room.generic
 have hh(y:↥(K*∩T)): ∀ᶠ i in atTop, dist (L (f.per i) y.val) (X y.val)≤δ:=by
    filter_upwards [hL n {y.val} isCompact_singleton (singleton_subset_iff.mpr y.property.1) w δ he', f.per.cofinal.eventually (Extraction.room C.S hT)] with i hr he
    rw [compatible_mesh (h _) f hP y.val ((no_wrap_tie C.S (he y.property.2)).2 y.property.1),dist_eq_norm]; exact (hr _ (Set.mem_singleton _)).le
 filter_upwards [(eventually_all_finset A).mpr (fun i _=> hh i),f.per.cofinal.eventually H] with i hi hU x h
 obtain ⟨y,hy⟩:= mem_iUnion.mp (hA h); obtain ⟨hY,hh⟩:= mem_iUnion.mp hy; let p:=f.per i
 have hl:dist x y.val<t:= Metric.mem_ball.mp hh; have hd': dist x y.val < d ∧ dist x y.val < r:= lt_min_iff.mp (hl.trans_le (min_le_left ..)); have ht':dist x y.val < δ/(1+b):= hl.trans_le (min_le_right ..)
 have he:=interior_subset (hv h); have hv:= y.property.2
 have hC: dist (L p x) (L p y.val) ≤ δ:= (hU y.val hv x he hd'.1).trans (by linarith [ ((lt_div_iff₀ (show 0<(1+b) from by positivity)).mp ht'),dist_nonneg (x:=x) (y:=y.val)])
 calc _≤ dist (L p x) (L p y.val)+ dist (L p y.val) (X y.val) +dist (X y.val) (X x) := le_trans (dist_triangle _ (L p y.val) _) (by have ht:=dist_triangle (L p y.val) (X y.val) (X x); change dist _ _ + dist _ (X x) ≤ _; linarith only [ht])
      _≤ δ+δ+δ:= add_le_add (add_le_add hC (hi y hY)) ((hR y.val hv x he (dist_comm y.val x ▸ hd'.2)).le)
      _≤ _:= by dsimp only [δ]; linarith
-- positions Rights. Need wrap tag exactly
abbrev again (f:Extraction.Order): Extraction.Order:= ⟨Extraction.Sequence.full,f.per⟩
def ClusterFrames (C:Family G) : Prop:= ∀ p n (w:Fin n→C.book.Token), ∃ L, Cluster C Extraction.Sequence.full p n (fun N=>lifted C N p w) L
variable (hp:ClusterFrames C)
include hp
theorem full (w: Fin n→ C.book.Token) {K:Set (Points n)}(hK:IsCompact K)(h:K⊆conf n)(ε:ℝ)(he:0<ε):
    ∀ᶠ i in (again f).fuse,∀ x:Positions n, Order.grid C i.1 x∈K→ ‖C.numeric i.1 i.2 w (wrap _ ∘ x) - S.read (Order.grid C i.1 x) w‖≤ ε:=by
 choose L H using fun p=> hp p n w; rw [Order.fused]; unfold Order.late
 filter_upwards [many F hF H hK h (ε/2) (half_pos he), f.per.cofinal.eventually (Extraction.room C.S hK)] with i hi hx
 let p:=f.per i; have hH : K⊆ NoHit C.S p n:= fun x h' => (no_wrap_hit C.S (hx h')).2 (h h'); filter_upwards [cluster_uniform (H p) hK hH (ε/2) (half_pos he)] with j hj u hU
 let x := Order.grid C j u; exact ((dist_eq_norm (lifted C j p w u) (S.read x w)).symm).trans_le ((dist_triangle _ (L p x) _).trans
    (by linarith only [show dist (lifted C j p w u) (L p x)≤ε/2 from hj u hU, (show dist (L p x) _ ≤ ε/2 from hi x hU) ]))
-- enough even over K varying with r,T when later date. No weak station etc assumptions needed here; user may exercise this receipt with PositionsUV in next file.
end YM.Integration.GradedFar.Auth

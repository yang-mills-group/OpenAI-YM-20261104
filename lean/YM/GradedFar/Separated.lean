import YM.GradedFar.ForkLedger
/-!
# For comparison, also traditional physical OPE estimates at ANY fixed-clearance Exterior (G.7)

As in bbcb. *Additional* price input here `L : Facilities ...`.
Use same F and Q; then `Q.packet` sum representative.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Finset Filter Function Set Spec Table Extraction OPE OPE.Orbits OPE.Log
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {I J:Type} [Fintype I] [Fintype J] (d:I→ℕ)(e:J→ℕ) (h:ℕ)
variable (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) {M δ c:ℝ} (hm:0≤M)(hd:0<δ)
    (bank:LogTrace F Q.port) (L : Facilities C f S)(hc:0<c)
local notation "Π₀" => Viewers F
local notation "Π₁" => Labels S d
local notation "Π₂" => Labels S e
local notation "Λ" => Sold (𝓝[>](0:ℝ))

-- contradiction version of cost at unbounded exterior row with fixed-physical near & labels
include L hc
lemma upTo (u : S.Field h) (w:Π₂) : ∃ b:ℝ, 0≤b ∧
    ∀ o y, ClearOf o y c → ∀ v, ‖upon (spectator F v) h o y w u‖ ≤ b := by
  by_contra! H
  choose o y hy v hv using (fun n:ℕ=> H _ (Real.exp_pos (2*n)).le)
  have ht:= tendsto_natCast_atTop_atTop (R:=ℝ)
  obtain ⟨hk,hx⟩:= free_clear ht hc (Eventually.of_forall hy)
  let a : Labels S (fun _:Unit=>h) := sole u
  have he:=viewer_cost F L.schedule (names a) (names w) ht v (Kept.sole atTop Nat.cast o 0) hk hx
    (le_refl 0) (le_refl 0)
  obtain ⟨i,hi,hn⟩:= ((he 1 (by simp)).and (eventually_gt_atTop 0)).exists
  have hp: (1:ℝ)*i <2*i:=by exact mul_lt_mul_of_pos_right (by norm_num) (by exact_mod_cast hn)
  have hQ:= hv i
  change Real.exp (2*(i:ℝ)) < ‖whole (spectator F (v i)) (sole (o i)) a (y i) w‖ at hQ
  rw [whole_observed] at hQ; exact (Real.exp_lt_exp.mpr hp).not_ge ((lt_of_lt_of_le hQ hi).le)

-- only fixed p & w needed to derive other prices uniformly
lemma capWave (w:Π₂):∃ b:ℝ,0≤b ∧ ∀ o y, ClearOf o y c → ∀ v u,
    ‖upon (spectator F v) h o y w u‖ ≤ b*‖u‖ := by
  -- finite actor basis or standard finrank
  have H (u) := upTo F e h L hc u w; choose b hb ha using H
  let B:=Module.finBasis ℂ (S.Field h); let g (i: Fin _) := LinearMap.toContinuousLinearMap (B.coord i)
  refine ⟨∑ i, b (B i) * ‖g i‖,Finset.sum_nonneg (fun i _=> mul_nonneg (hb _) (ContinuousLinearMap.opNorm_nonneg _)),?_⟩
  intro o y c v u
  conv_lhs=> rw [← B.sum_repr u,map_sum]
  simp_rw [map_smul]
  rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_)
  rw [norm_smul]; change ‖g i u‖*_ ≤ _; refine (mul_le_mul ((g i).le_opNorm _) (ha (B i) o y c v)
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

omit L hc

variable {F} in
structure Housing (F:Final C f S) (I J:Type) where
    launch : Launch I
    viewer : Viewers F
    perspective : J→E4

variable {F} in
def Deluxe (M δ c:ℝ) (r:ℝ)(p: Housing F I J):= Tiny M δ r p.launch ∧ ClearOf p.launch.center p.perspective c

def trueError (x:I→E4)(o:E4)(y:J→E4)(v:Π₀) :
    MultilinearMap ℂ (fun i=> S.Field (d i)) (MultilinearMap ℂ (fun i=> S.Field (e i)) ℂ) :=
  trace F x y v - (watch F y o h v).compMultilinearMap (packetCost F x o h Q)

lemma trueError_apply (x:I→E4)(o:E4)(y:J→E4)(v:Π₀)(u: Labels S d)(w: Labels S e):
    trueError F d e h Q x o y v u w= whole (spectator F v) x u y w-upon (spectator F v) h o y w (Q.packet h x u o) := by
  change trace F x y v u w-watch F y o h v (packetCost F x o h Q u) w=_
  rw [trace_apply,packetCost_apply,watch_apply]

include L hc bank hm hd
lemma adequate (u:Π₁)(w:Π₂): Λ (Deluxe M δ c) TagCost (wage d h)
    (fun _ (p:Housing F I J)=> trueError F d e h Q p.launch.x p.launch.center p.perspective p.viewer u w) := by
  obtain ⟨b,hb,hQ⟩:= capWave F e h L hc w
  let s (p:Housing F I J):= shadowError F p.launch.x p.perspective p.launch.center h p.viewer Q.port u w
  let T (p:Housing F I J):= upon (spectator F p.viewer) h p.launch.center p.perspective w (LedgerR F d Q h p.launch u)
  have hv: Λ (Deluxe M δ c) TagCost (wage d h) (fun _ p=> s p) := by
    obtain ⟨k,hk⟩:= OnLog F d h Q bank hm hd e hc u w
    exact ⟨k,1,by norm_num,hk.mono fun r hr p hp=> by rw [one_mul]; exact (hr p.launch hp.1 p.perspective hp.2).2.2 p.viewer⟩
  have hR : Λ (Deluxe M δ c) TagCost (wage d h) (fun _ p=> T p):= by
    apply ((CostedR F d h Q hm hd bank u).rename (p:=id) tendsto_id (y:=fun _ (p:Housing F I J)=> p.launch)
      (A:=Deluxe M δ c) (Eventually.of_forall (fun r p hp=>hp.1))).transfer hb
    exact Eventually.of_forall fun r p hp=> hQ _ _ hp.2 p.viewer _
  apply (hv.sub (wage_ok d h _) hR).congr; intro _ p
  rw [trueError_apply]; unfold s T; rw [shadowError_apply, settlePacket,map_sub,discrepancy]; abel

theorem G7 (b:ℝ)(hb:0≤b):∃ k:ℕ, ∃ D:ℝ, 0≤D ∧ ∀ᶠ r:ℝ in 𝓝[>]0,
    ∀ o x y, WithinRoom r M δ x o → ClearOf o y c →
    Injective (beside x y) ∧ Injective (beside (sole o) y) ∧
    ∀ (v:Π₀) (u:Π₁) (w:Π₂), (∀ i,‖u i‖≤b) → (∀ i,‖w i‖≤b) → ‖Orbits.formula F Q x o u y w h v‖ ≤
      D*badge r^k*(r^(h+1)/r^(∑i,d i)):=by
  obtain ⟨k,D,hD,H⟩:=Sold.both (wage_ok d h _) (adequate F d e h Q hm hd bank L hc) b hb
  obtain ⟨j,hj⟩:=bank.horizons I J (fun _=>C.book.one 0) (fun _=>C.book.one 0) δ M c hd hm hc h
  refine ⟨k,D,hD,?_⟩; filter_upwards [H,hj] with r hr hj o x y hx hy; obtain ⟨h0,h1,_⟩:= hj x y o hx hy
  refine ⟨h0,h1,?_⟩
  intro v u w hu hw; specialize hr (⟨⟨x,o⟩,v,y⟩:Housing F I J) ⟨hx,hy⟩ u w hu hw
  rw [Orbits.formula,← packet_read F Q x o u y w v h h1]; rw [trueError_apply] at hr; exact hr
end YM.Integration.GradedFar.Fork

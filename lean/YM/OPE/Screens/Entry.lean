import YM.OPE.Screens.Meter
/-!
# Fixed far scopes are enough for all rows
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Shuttle
open Function Filter Finset MeasureTheory Lattice RG Wilson Next.UVStress Spec Cards
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G:Gauge}
    {k b n m l q u j p N W :ℕ} {C: Family G} {c A α η:ℝ}
    {F:Extraction.Order} {S:Table C.book}(U:Final C F S) {x:J→ Cover}{Y:J→ E4}
    {v:J→ C.book.Token}
namespace Probe
local notation "μ"=> C.S.a
variable {X':Cylinder C}{f: Filter (ℕ×ℕ)}[f.NeBot] (h:f≤ F.fuse)
structure Viewer (C:Family G)(F:Extraction.Order)(v:J→ C.book.Token)(q:ℕ)(c α:ℝ): Prop where
    here : ∃ b l u W, ∃ y:J→ℝ, Hall C.S b l q u W 1 (Fintype.card J)∧ 2*C.S.a b<c∧ Prepared (C:=C) v F W y∧α=∏ i,y i
variable (B:Viewer C F v q c α) {L:Fin n → Spark C f k}
include h U B
lemma sold (D:Org.Grill C F)(a:Fin n→ℂ)(hq:q ≤ k)(hp: ∀ᶠ i:ℕ×ℕ in f,PaidAt C.S i.1 i.2 q (C.beta i.1 i.2) A (X' i.1 i.2))(hE:∀ᶠ i:ℕ×ℕ in f,(fun U:Config G (C.side i.1 i.2)=> ∑ j:Fin n,a j*(L j).cuts i.1 i.2 U)=X' i.1 i.2)(hx:∀ i,Injective (beside (point (L i)) Y))(hc:ClearOf 0 Y c) : ‖∑ i,a i • view U (L i) v Y‖ ≤ A*α:=by
    obtain ⟨b,l,m,W,u,hT,hu,hU,ht⟩:= B.here; subst α; refine border U h D a L hT hU hp hE (hT.first.trans (hT.third.trans hq)) hx ?_ (fun _ j=> hu.trans_le (hc.openSpace _)); have hf:= C.S.strictAnti.antitone (hT.first.trans hT.second); exact fun i j he=> (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hf zero_le_two) hu).trans_le (hc.spread _ _ he)
omit h B
lemma arrivals (v:J→ C.book.Token) (hc:0<c) : ∀ᶠ q in atTop,∃ b, Viewer C F v q c b:=by
    -- b unaligned.Late means b constant any.
    let S:= C.S; have he (u:ℝ): Tendsto (fun i=>u*S.a i) atTop (𝓝 0):=by simpa only [mul_zero] using (S.shrinks.const_mul u)
    obtain ⟨j,hj⟩ :=((he 2).eventually (gt_mem_nhds hc)).exists; obtain ⟨f,hf,hP⟩:= ((eventually_ge_atTop j).and ((he 10).eventually (gt_mem_nhds (S.a_pos j)))).exists; let M:=(Fintype.card J:ℝ); have ht:Tendsto S.scale atTop atTop:= S.divergent; have hQ:Height C.S atTop S.scale id 1:= ⟨tendsto_id,tendsto_const_nhds.congr' ((ht.eventually_gt_atTop 0).mono fun i hi=> (div_self (show S.scale i≠ 0 from hi.ne')).symm)⟩; obtain ⟨A,hA,hY⟩:= admitted U v ht hQ zero_lt_one
    obtain ⟨N,hN,hW,hZ⟩:= ((eventually_ge_atTop f).and (hY.and ((he (M*6)).eventually (gt_mem_nhds (S.a_pos f))))).exists; have hh: M * (2*(3*C.S.a N)) < C.S.a f:=by change M*6*S.a N < _ at hZ; unfold S at hZ; linarith only [hZ]
    filter_upwards [eventually_ge_atTop f] with q hq; exact ⟨_, _,_,_,_,_,⟨hf, le_rfl,hq,hN,(by norm_num only [Nat.cast_one]; change 10 * S.a f < S.a j at hP; unfold S at hP; linarith only [hP]), hh⟩,hj,hW,rfl⟩
end Probe
-- constructors for Spark
variable {f: Filter (ℕ×ℕ)} {p':I→ C.book.Token} {x':I→ Cover}
    {V : ReadLabel C p'}{z:ℕ×ℕ→ C.label n} {y:C.label n}
def seen (hp:Screen (C.S.gridPoint k ∘ x'))(h:∀ i,Tendsto (V i) f (𝓝 (p' i).2)): Spark C f k:= ⟨I,x',p',V,h,hp⟩
local notation "g!"=> (fun _ :Unit=> (0:Cover))
def host (hp:Tendsto z f (𝓝 y))(k:ℕ): Spark C f k:= {Index:=Unit, x:=fun _=>0, v:=fun _=> ⟨n,y⟩, q:=fun _=>z, limit i:=hp, frames:=fun _=> injective_of_subsingleton _ }
def betweenRows (p q: Spark C f k) (h:Screen (beside (Probe.point p) (Probe.point q))): Spark C f k:= { Index:=p.Index⊕ q.Index,x:=beside p.x q.x, v:=beside p.v q.v, q:= combine p.q q.q, limit i:=by cases i; exact p.limit _; exact q.limit _, frames:=by rw [beside_commutes]; exact h }
lemma exchangeShips (p q:Spark C f k)(h:Screen (beside (Probe.point p) (Probe.point q))): Probe.point (betweenRows p q h)=beside (Probe.point p) (Probe.point q) := beside_commutes p.x q.x (C.S.gridPoint k) -- state type explicitly
lemma exchangeProducts (p q:Spark C f k)(h:Screen (beside (Probe.point p) (Probe.point q))): (betweenRows p q h).cuts = p.cuts * q.cuts:=funext fun i=>funext fun j=> works p.q q.q k i j p.x q.x
lemma hostcut (hp:Tendsto z f (𝓝 y)) (k:ℕ): (host hp k).cuts = stampEntry n z:=by funext i j; exact just_one (stampEntry n z) k i j -- unfolding
lemma hostPoint (hp:Tendsto z f (𝓝 y)) : Probe.point (host hp k)= sole (0:E4):= funext fun i=> grid_zero ..
end YM.OPE.Log.Trunk.Shuttle

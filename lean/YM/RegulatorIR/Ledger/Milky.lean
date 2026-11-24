import YM.RegulatorIR.Ledger.Sky

/-! Vacuum propagation through a whole list. `WayO` payments involve strictly
smaller coupling orders only and may have post-block constants for them. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger.Sky
open Budget Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W: Type} {M:W→ℕ} {X Y:Page M→Type} (S:Sky X Y) (T:S.Accounts)
variable {u b p e r:ℕ}{L:Meter W} {c: Flap M→ℝ≥0∞}

/-- Initial chart + quotient-vs-bulk Ward equation. No conjecture on small
repairs or locality of defects in this hypothesis. -/
structure Cosmos (u b p:ℕ)(L:Meter W):Prop where
  prim : S.Primitive L p (u+b+(u+b))
  space : S.Supplies T L p (u+b+(u+b))
  tops : ∀ w i j,i ≤ p → 0<j → T.change (Page.opening M w) i j=0
  ward : ∀ w i,i ≤ p → (S.sight w).WayO (T.change w.prev) i
  counted : Poly (flapL M L) (S.ceilingRoom.weight b)

variable [∀ w,Fintype (Y w)]
-- unfolding well-founded def manually for kernel
private lemma once (H:S.Cosmos T u b p L) (hh: ∀ i j, Earlier e r i j → 0<j → Claim (coverL M L) (S.census.pear u) 1 (fun w=> T.change w i j)) (hp:e ≤ p)(hr:0<r):
   Claim (flapL M L) (fun w:Flap M=> S.census.pear u w.next) 1 (fun w=>T.change w.next e r- updateQ (S.sight w).tunnel (T.change w.prev e r) 0) := by
 let F:= S.lifts; let l:= S.ceiling
 have hm : Beam (flapL M L) (S.ceilingRoom.cone u) S.lifts.forecast:= S.ceilingRoom.descent H.prim.drift (by omega)
 have hx i j (he:Earlier e r i j)(hc:0<j):Claim (flapL M L) (S.bar.pear u) 1 (fun w=> T.change w.prev i j):= by
   have hH : Claim (flapL M L) (S.carryUp.pear u) 1 (fun w=> T.change w.prev i j):= Claim.us (hh i j he hc) Flap.prev
   exact Post.fewer (M:=S.carryUp) (l:=S.ceiling) S.high (fun w=> S.climb w) hH
 let g:= fun w:Flap M=> F.kick (fun w:Flap M=> T.change w.prev e r) w
 -- create local instances
 letI : ∀ w:Flap M,Fintype (Y w.prev):= fun w=> inferInstance
 letI : ∀ w:Flap M,Fintype (Y w.next):= fun w=> inferInstance
 have hf : Claim (flapL M L) (fun w:Flap M=> S.census.pear u w.next) 1 (fun w=> T.change w.next e r-g w):= by
    have he:= Batch.assembly S.lifts (fun w=> T.bulk w.prev) (fun w=> T.orb w.prev) (b:=b) (u:=u) (e:=e) (r:=r) H.prim.line H.counted H.prim.deckLine (fun w i j he=> H.prim.deckAdd w i j (he.trans hp)) (fun w i j he=> H.space.bulk_deck _ i j (he.trans hp)) H.prim.grade (fun w=> T.cap_b H.prim.grade _) (fun w=> T.cap_o H.prim.grade _) (fun i he=> T.deposit H.space i (he.trans hp)) (fun i he=> H.prim.add_cost i (he.trans hp)) hx hm H.prim.deckDrift hr
    convert he using 1 <;> try rfl
    ext1 w; unfold Accounts.change Uniform.Post.vgap
    rw [← T.step_o w,← T.step_v w]; rfl
 have hq : Claim (flapL M L) (fun w:Flap M=> S.census.pear u w.next) 1 (fun w=> g w- updateQ (S.sight w).tunnel (T.change w.prev e r) 0):= Batch.recover (F:=S.lifts) (T:=fun w=>T.change w.prev) S.sight (fun w=> Premium.remnant _ (F.positive w) _ (S.high w) u) (fun i he=> H.prim.charges u (by omega) i (he.trans hp)) (fun i h j hr=>hx i j (Or.inl h) hr) H.prim.ground (fun w=>H.ward w e hp) (wrap_beam _ hm H.prim.deckDrift)
 convert hf.add hq using 1; ext1 w; abel

lemma across (H:S.Cosmos T u b p L) (hh:∀ i j,Earlier e r i j → 0<j → Claim (coverL M L) (S.census.pear u) 1 (fun w=> T.change w i j)) (hm:S.Lead u c) (hp:e ≤ p)(hr:0<r):
   Claim (coverL M L) (S.census.pear u) 1 (fun w=> T.change w e r):=by
 let q (w:Page M):= markQ (S.census.pear u w) (T.change w e r)
 let U:=fun w: Flap M=>updateQ (S.sight w).tunnel (T.change w.prev e r) 0
 let g w:=(T.change (Flap.next w) e r-U w)
 let f(w:Flap M):=markQ (S.census.pear u w.next) (g w)
 have hg : Carry (flapL M L) 1 f:= once S T H hh hp hr
 change Carry (coverL M L) 1 q
 refine turning q (v:=fun _=> 1) (F:=f) hg ?_ H.prim.depth ?_
 · intro w
   have hu : markQ (S.census.pear u w.next) (U w) ≤ markQ (S.bar.pear u w) (T.change w.prev e r)*c w^r:= by
     let P := Premium.remnant (S.P w.volW) (S.hp w.volW) _ (S.high w) u
     exact (S.sight w).tunnel_price (H.prim.ground w) (S.hp w.volW) (S.high w) P (ne_top_of_le_ne_top ENNReal.one_ne_top (hm.cap w)) (hm.down w) _ (by rw [quota_base]; exact tsum_enorm_ne_top_iff_summable_norm.mpr (hasSum_fintype ..).summable)
   have hz : markQ (S.census.pear u w.next) (U w) ≤ q w.prev:=hu.trans (calc
     _ ≤ markQ (S.bar.pear u w) (T.change w.prev e r)*1:= mul_le_mul_right (pow_le_one₀ (by positivity) (hm.cap _)) _
     _ ≤ _:= by rw [mul_one]; exact Post.place_fewer (M:=S.carryUp) S.high (fun w=>S.climb w) w _)
   let C:= S.census.pear u w.next
   calc
    _= markQ C (U w+g w):= by rw [show U w+g w= T.change w.next e r by unfold g;abel]
    _ ≤ markQ C (U w) + markQ C (g w):=quota_add ..
    _ ≤ _:= add_le_add_left hz _
 refine Carry.mono (Carry.zeroQ _) (fun w=> ?_)
 change q _ ≤ (0:ℝ≥0∞); unfold q; rw [H.tops w e r hp hr];exact (quota_zero _).le

/-- Arbitrary-order point-localization on the singular sets, including
inherited defects hit by other defects and repeated order diagonal. -/
theorem confined (H:S.Cosmos T u b p L) (hm:S.Lead u c):∀ e ≤ p,∀ r:ℕ, 0<r → Claim (coverL M L) (S.census.pear u) 1 (fun w=> T.change w e r):= by
 apply editions (fun i=> i+2) 1 (P:=fun e r=> Claim (coverL M L) (S.census.pear u) 1 (fun w=> T.change w e r)) (fun i he j hj _ hP=>across S T H hP hm he hj)
 intro i he j hm _
 have h w : T.change w i j=0:=by
   have he:T.bulk w i j=0:=Classical.byContradiction fun h=> not_lt.mpr (T.cap_b H.prim.grade w i j h).2 hm
   have hx:T.orb w i j=0:=Classical.byContradiction fun h=> not_lt.mpr (T.cap_o H.prim.grade w i j h).2 hm
   unfold Accounts.change; rw [he,hx,Deck.desk_zero,sub_self]
 simp_rw [h]; exact Claim.zeroQ
end YM.RegulatorIR.Ledger.Sky

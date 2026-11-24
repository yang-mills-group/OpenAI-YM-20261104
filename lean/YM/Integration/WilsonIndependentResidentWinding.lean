import YM.Integration.WilsonIndependentFreshDeviationWard
import YM.RegulatorIR.Ledger.Ori

/-! The period estimate with the authentic incoming unmarked winding on a
nonbare interval. A fresh marked input still has its exact initial fold. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentResidentWinding
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Budget Spatial Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W: Type} {M:W→ℕ} {X Y:Page M→Type} (S:Sky X Y) (T:S.Accounts)
variable {m:ℕ} (G:T.Report m)
variable {a r e p u b q:ℕ}{c t : Flap M→ℝ≥0∞}{x:W→Room}{s:W→ℝ≥0∞}{L:Meter W}
-- t is cost of source (finer scaling may be huge); s buys tolls -> estimated
structure Resident (a q p : ℕ) (L : Meter W) : Prop where
  prim : S.Primitive L p (a+q+(a+q))
  space : S.Supplies T L p (a+q+(a+q))
  counted : Poly (flapL M L) (S.ceilingRoom.weight q)
  prior : ∀ i, i ≤ p → ∀ r, 0 < r → Claim (coverL M L) (S.census.pear a) 1
    (fun w => T.change w i r)

theorem inherited [∀ w, Fintype (Y w)] (E : Era M) (H : S.Cosmos T a q p L)
    (course : S.Lead a c) : Resident (E.expanse S) (E.part S T H.prim) a q p L where
  prim := E.sector S H.prim
  space := E.getN S H.space H.prim
  counted := H.counted.us E.wing
  prior i hi r hr := (S.confined T H course i hi r hr).us E.page

section
variable [∀ w,Fintype (Y w)]
private lemma single (H:Resident S T (u+b) q p L) (_hm:S.Lead (u+b) c) (B: S.Price T G u b p x s t L)
 (hx:∀ i j,Earlier e r i j → 0<j → Claim (coverL M L) (S.markUp x u) (fun w=>s w.bindW) fun w=> G.deviation w i j) (he:e≤p): Claim (flapL M L) (fun w:Flap M=>S.markUp x u w.next) (fun w=>s w.volW) fun w=>G.deviation w.next e r-updateQ (S.sight w).tunnel (G.deviation w.prev e r) 0:=by
 have hdata:= H.prior
 have hV i (hi:i≤p) j (hj:0<j):Claim (flapL M L) (S.bar.pear (u+b)) 1 (fun w=> T.change w.prev i j):=by
    have h : Claim (flapL M L) (S.carryUp.pear (u+b)) 1 (fun w=> T.change w.prev i j) := Claim.us (hdata i hi j hj) Flap.prev
    exact Post.fewer (M:=S.carryUp) S.high (fun w=> S.climb w) h
 have hT i j (hh:Earlier e r i j) (hj:0<j) : Claim (flapL M L) (S.Plaza x u) (fun w=>s w.volW) (fun w=> G.deviation w.prev i j):= by
    have h : Claim (flapL M L) (S.camp.anchored (step_center M x) u) (fun w=>s w.volW) (fun w=> G.deviation w.prev i j):= Claim.us (hx i j hh hj) Flap.prev
    exact Post.few_orb S.ridge_pos (M:=S.camp) (l:=S.ridge) (fun w=> S.radius_climb w) h
 let f w:= S.lifts.kick (fun w=> G.deviation w.prev e r) w
 let A:= S.lifts
 have hM:= S.get_drift H.prim (show u≤u+b+q+(u+b+q) from by omega)
 letI : ∀ w:Flap M,Fintype (Y w.prev):= fun w=> inferInstance
 letI : ∀ w: Flap M,Fintype (Y w.next):= fun w=>inferInstance
 have hα : Claim (flapL M L) (fun w:Flap M=> S.markUp x u w.next) (fun w=>s w.volW) fun w=> G.deviation w.next e r-f w:=by
    have he' := Batch.node S.lifts (fun w=> T.bulk w.prev) (fun w=> T.orb w.prev) (fun w=> G.main w.prev) (fun w=> G.point w.prev) (e:=e) (r:=r) (q:=q) (u:=u) (b:=b) (l:=S.ridge) (l₀:=S.ceiling) (x:=step_center M x) S.ridge_more H.prim.line H.counted H.prim.deckLine (fun w i j hi=> H.prim.deckAdd w i j (hi.trans he)) (fun w i j hi=> H.space.bulk_deck w.prev _ _ (hi.trans he)) H.prim.grade (fun w=> T.cap_b H.prim.grade _) (fun w=> T.cap_o H.prim.grade _) (fun i hi=> T.deposit H.space i (hi.trans he)) (fun i hi=> H.prim.add_cost i (hi.trans he)) (fun i hi=>hV i (hi.trans he)) (fun i hi=>B.data i (hi.trans he)) B.coin B.ticket hT hM H.prim.deckDrift m
    convert he' using 1 <;> try rfl
    ext1 w
    unfold Accounts.Report.deviation Post.agap
    rw [← G.step_p w,← G.step_m w]; rfl
 have hβ : Claim (flapL M L) (fun w:Flap M=> S.markUp x u w.next) (fun w=>s w.volW) fun w=> f w-updateQ (S.sight w).tunnel (G.deviation w.prev e r) 0:=
    Batch.recover (F:=S.lifts) (T:=fun w=>G.deviation w.prev) S.sight (fun w=> Premium.rooted (onFold _ (A.positive w) _ (S.ridge_pos w) u) (x w.volW)) (fun i hh=> S.adv_pair H.prim (by omega) i (hh.trans he)) (fun i h j hj=>hT i j (Or.inl h) hj) H.prim.ground (fun w=> B.ward w e he) (wrap_beam _ hM H.prim.deckDrift)
 convert Claim.add hα hβ using 1; ext1 w; abel

private lemma flap_price (H:Resident S T (u+b) q p L)(hm:S.Lead (u+b) c)(B:S.Price T G u b p x s t L)
   (hx:∀ i j,Earlier e r i j → 0<j → Claim (coverL M L) (S.markUp x u) (fun w=>s w.bindW) fun w=> G.deviation w i j)(he:e≤p): Claim (coverL M L) (S.markUp x u) (fun w=>s w.bindW) fun w=> G.deviation w e r:=by
 let Z w:= updateQ (S.sight w).tunnel (G.deviation w.prev e r) 0
 have hf := single S T G H hm B hx he
 let f w:= markQ (S.markUp x u w) (G.deviation w e r)
 refine turning f hf ?_ H.prim.depth ?_
 · intro w
   let C:= S.markUp x u w.next
   have hp: markQ C (Z w) ≤ markQ (S.Plaza x u w) (G.deviation w.prev e r)*c w^r:=by
      let P:= Premium.rooted (onFold _ (S.lifts.positive w) _ (S.ridge_pos w) u) (x w.volW)
      exact (S.sight w).tunnel_price (H.prim.ground w) _ _ P (ne_top_of_le_ne_top ENNReal.one_ne_top (hm.cap _)) (S.pole_cost hm (by omega) w) _ (by rw [quota_base]; exact tsum_enorm_ne_top_iff_summable_norm.mpr (hasSum_fintype ..).summable)
   have ht : markQ C (Z w) ≤ f w.prev:= hp.trans (calc
     _ ≤ markQ (S.Plaza x u w) (G.deviation w.prev e r)*1 := mul_le_mul_right (pow_le_one₀ (by positivity) (hm.cap _)) _
     _ ≤ _:= by rw [mul_one]; exact Post.orb_fewer (x:=step_center M x) S.ridge_pos (M:=S.camp) (fun w=> S.radius_climb w) w _)
   let P:= G.deviation w.next e r-Z w
   calc
    _= markQ C (Z w+P):=by rw [show Z w+P=G.deviation w.next e r by unfold P; abel]
    _ ≤ markQ C (Z w)+markQ C P:=quota_add ..
    _ ≤ _:=add_le_add_left ht _
 refine Carry.mono (Carry.zeroQ _) (fun w=>?_)
 change f _ ≤ (0:ℝ≥0∞); unfold f Accounts.Report.deviation; rw [G.same,sub_self]; exact (quota_zero _).le

/-- Uniform in center addresses and number of continuation steps, with
root norm and scalar cost. The ticket is normally bought by the fourth-root
period or similar (later adapter); only cover inputs need extra moments. -/
theorem archive (H:Resident S T (u+b) q p L) (hm:S.Lead (u+b) c)(B:S.Price T G u b p x s t L):∀ e≤p,∀ r:ℕ, Claim (coverL M L) (S.markUp x u) (fun w=>s w.bindW) fun w=> G.deviation w e r:=by
 have h (i:ℕ)(he:i≤p) (j) (hh:i+m<j): Claim (coverL M L) (S.markUp x u) (fun w=>s w.bindW) fun w=> G.deviation w i j:=by
   have hv w : G.deviation w i j=0:=by
     have he:G.main w i j=0:=Classical.byContradiction fun h=> not_lt.mpr (G.cap_b H.prim.grade w i j h) hh
     have hm:G.point w i j=0:=Classical.byContradiction fun h=> not_lt.mpr (G.cap_o H.prim.grade w i j h) hh
     rw [Accounts.Report.deviation,hm,he,Deck.scroll_zero,sub_self]
   simp_rw [hv]; exact Claim.zeroQ
 exact fun e hp r=> editions (fun i=>i+m) 0 (P:=fun e r=> Claim (coverL M L) (S.markUp x u) (fun w=>s w.bindW) fun w=> G.deviation w e r) (fun i hi j _ _ hP=>flap_price S T G H hm B (fun i j hp hj=>hP i j hp (by omega)) hi) (fun i hi j hh _=> h i hi j hh) _ hp r (by omega)
end
end YM.Integration.WilsonIndependentResidentWinding

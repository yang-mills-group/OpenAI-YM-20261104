import YM.WilsonCoeffUV.Emit.LayoutCosts
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Layout
open Wheel.ScaleS Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost Physical
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Wheel.Flooring Ticket
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{V W:Credit}{m b j e a D d:ℕ}{R:Realm G e V}{r z A:ℝ}{x:Cover}

/-! Actual compact shapes as normalized product factors at reporting radius,
center evaluation in k-cell units and ℓ∞ norm `Point4`. `A` amplitude restored per slot. -/
def zoom (φ:Rarity D)(r:ℝ) : Phrase D:= r⁻¹^4 • sonal r⁻¹ 0 zeroC 0 φ.ψ
lemma towards0 (t:ℝ)(x:Point4): address t 0 zeroC (0:Cover) x = t • x:=by unfold Mer.address Mer.position Mer.actualW; rw [show (fun i=> (↑((0:Cover) i):ℝ))=0 by ext i; simp]; simp
lemma zoom_at (φ:Rarity D)(r:ℝ)(x:Point4): (zoom φ r).val x=r⁻¹^4*(φ.ψ.val (r⁻¹ • x)):=by
    change r⁻¹^4*φ.ψ.val _=_; rw [towards0]
lemma support_zoom (φ:Rarity D)(r:ℝ): ∀ x ∈ tsupport (zoom φ r).val,r⁻¹ • x ∈ tsupport φ.ψ.val:=by
   let T:= tsupport φ.ψ.val
   refine closure_minimal (t:=(fun x:Point4=>r⁻¹ • x) ⁻¹' T) ?_ (isClosed_closure.preimage (by fun_prop))
   intro i p; refine Set.mem_preimage.mpr (Set.mem_of_mem_of_subset ?_ subset_closure); exact fun h=> p (by rw [zoom_at,h,mul_zero])
lemma support_pay (p:0<r)(f:Rarity D) : tsupport (zoom f r).val ⊆ Metric.closedBall 0 (f.radius*r):=by
   intro i x; have hp:= f.support (support_zoom f r i x); simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos p] at hp ⊢; rwa [mul_comm,← div_eq_mul_inv, div_le_iff₀ p] at hp
-- geometry exact
abbrev farther (q:1≤ r)(P:Rarity D) : Rarity D:= ⟨zoom P r,P.radius*r,one_le_mul_of_one_le_of_one_le P.markG q,support_pay (zero_lt_one.trans_le q) P⟩
lemma clearance {P:Rarity D}{Q:Rarity d}{c:ℝ}(v: ClearDay P Q c)(u:1≤ r): ClearDay (farther u P) (farther u Q) (c*r):=by
   intro x p y q; have hp:= v _ (support_zoom P r x p) _ (support_zoom Q r y q); have hz:0<r:= zero_lt_one.trans_le u
   rwa [dist_eq_norm,← smul_sub,norm_smul, Real.norm_eq_abs,abs_inv,abs_of_pos hz,← dist_eq_norm,mul_comm,← div_eq_mul_inv,le_div_iff₀ hz] at hp
lemma zoom_charge (q:1≤ r)(P:Rarity D)(f:Amplitude P A): Amplitude (farther q P) (r⁻¹^4*A):=by
   have hv:=f.1; have he:0<r:=zero_lt_one.trans_le q
   refine ⟨mul_nonneg (by positivity) hv,fun i h v t=>?_⟩; change ‖iteratedFDeriv ℝ i (r⁻¹^4 • (sonal r⁻¹ 0 zeroC 0 P.ψ).val) t _‖≤_
   rw [show iteratedFDeriv ℝ i (r⁻¹^4 • _) t = _ from iteratedFDeriv_const_smul_apply (a:=r⁻¹^4) (x:=t) (scribble (sonal r⁻¹ 0 zeroC 0 P.ψ) h).contDiffAt]; change ‖r⁻¹^4 • crease (sonal r⁻¹ 0 zeroC 0 P.ψ) v t‖≤_; rw [currentP _ _ _ _ _ _ h, norm_smul, norm_mul,norm_pow,norm_pow,Real.norm_of_nonneg (show 0≤ r⁻¹ by positivity : 0≤ r⁻¹)]
   exact mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left (f.2 _ h _ _) (by positivity)) (mul_le_of_le_one_left hv (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ q)))) (by positivity)
section
variable {T:Fin (a+1)→SealR G}{Φ:Wilt T}{U: Credit}{B:Fin (a+1)→ℝ}{b':ℕ}
structure Scenery (T:Fin (a+1)→SealR G)(f: Wilt T)(R:ℕ)(d:ℝ)(A: Fin (a+1)→ℝ):Prop where
   pos:0<d
   sizeT :∀ i,(f i).radius ≤ R
   gaps i j :i≠j→ ClearDay (f i) (f j) d
   stations i: Amplitude (f i) (A i)
abbrev sceneGrow (h:1≤ r) (X: Wilt T): Wilt T:= fun i=> farther h (X i)
lemma bough_bill (P:Credit)(d:ℝ)(b':ℕ):∃ X:Credit,∀ (T:Fin (a+1)→SealR G)(R:Realm G e V)(_v:R.y=zz R.draws) a m b j r (_p:Windows R.draws a m b j r)(t:1≤r)(φ:Wilt T)(A), r≤ P.buy (longLog R.draws m)→ R.anchor≤ j→ Scenery T φ b' d A → Bough T (sceneGrow t φ) (paceT R.draws.S m b) (X.buy (longLog R.draws m)) (fun i=> r⁻¹^4*A i)∧ Compar R.draws.S R.y j m ≤ X.buy (longLog R.draws m):=by
   obtain ⟨Z,U,h⟩:= soft_cost (G:=G) (e:=e) P V
   let F:=pur (d⁻¹); let X:= (pur (b':ℝ)).prodC (P.prodC V); let L:= (X.plus F).plus Z
   refine ⟨L,fun T R V' a' m b j r p t φ A hr q hp=>?_⟩; let z:=longLog R.draws m; have hx:1≤ z:=by linarith [long_pos R.draws m]
   have hz:1≤ L.buy z:= L.purchase hx; let s i:= P.buy i; let k:= paceT R.draws.S m b; have hK: k ≤ X.buy z:= (disCC p (q.trans p.soft.le) (zero_le_one.trans t) P hr V').trans (by unfold X; rw [Credit.products (pur (b':ℝ)) (P.prodC V)]; exact le_mul_of_one_le_left (zero_le_one.trans (Credit.purchase _ hx)) (Credit.purchase _ hx))
   have hv:X.buy z+F.buy z+Z.buy z≤ L.buy z:=(add_le_add_left (Credit.fuel X F hx) _).trans (Credit.fuel (X.plus F) Z hx)
   have hZ:X.buy z≤ L.buy z:= by linarith only [F.purchase hx,Z.purchase hx,hv]
   have he := h R a' m b j r p q t hr V'; refine ⟨⟨hz,(fun i=>zoom_charge t (φ i) (hp.stations i)),fun i=>?_,(by rw [abs_of_pos (pace_pos ..)]; exact hK.trans hZ),fun i j n=>?_⟩, he.1.trans (by linarith only [F.purchase hx,X.purchase hx,hv])⟩
   · change (φ i).radius*r≤_; apply le_trans _ hZ; unfold X; rw [Credit.products]; exact mul_le_mul (le_trans (hp.sizeT i) (pure_goal ..)) (p.firstC.trans (disCC p (q.trans p.soft.le) (zero_le_one.trans t) P hr V')) (zero_le_one.trans t) (zero_le_one.trans (Credit.purchase _ hx))
   intro a ha b hb
   have hF:F.buy z≤ L.buy z:= by linarith only [X.purchase hx,Z.purchase hx,hv]
   exact le_trans ((inv_le_comm₀ (zero_lt_one.trans_le hz) hp.pos).mpr ((show d⁻¹ ≤ F.buy z from pure_goal ..).trans hF)) ((le_mul_of_one_le_right hp.pos.le t).trans (clearance (hp.gaps i j n) t _ ha _ hb))
end
end YM.WilsonCoeffUV.Layout

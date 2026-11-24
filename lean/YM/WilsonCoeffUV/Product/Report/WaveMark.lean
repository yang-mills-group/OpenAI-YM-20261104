import YM.WilsonCoeffUV.Product.Report.Motif
/-!
# First-join UV rate with physical supports
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost PowerSeries
open scoped Matrix.Norms.Frobenius
variable {b b' u m M N a:ℕ}{H:Hol G} {δ Z y:ℝ} {E W V' W':Credit}{R:Realm G (e+1) E}
variable {Q:Fin (a+1)→ SealR G}{T:Wilt Q}{F:Fin (a+1)→ℝ}
lemma vacant (S:Levels G)(Ñ:ChartRatio G)(φ:Wilt Q)(o:CellR)(w:Fin (a+1))(v:¬ (VisitsT (φ w) (paceT S.S m i) y o).Nonempty) (t:Herit Q): awaken Q S Ñ φ t m i N y o w=0:=by
    unfold awaken arouse SealR.spins FirstCharge; rw [pupil_eye _ _ _ _ _ _ (pace_pos ..),Finset.not_nonempty_iff_eq_empty.mp v,Finset.sum_empty]
lemma boughRise {Z':ℝ}(p:Bough Q T y Z F)(g:Z≤ Z'): Bough Q T y Z' F:=⟨p.pos.trans g,p.lanes,fun i=>(p.rents i).trans g,p.room.trans g,fun i j v a h b e=>(inv_anti₀ (zero_lt_one.trans_le p.pos) g).trans (p.seats i j v a h b e)⟩

lemma waveMark (H:Hol G)(Q:Fin (a+1)→SealR G)(E W V W':Credit)(e u d:ℕ): ∃ C:Credit,∀ (R:Realm G (e+1) E), HorizonP H R W V Q→ SpringD R (capP Q) u (capP Q+d) W' →∀ m i b N M (F: Wilt Q)(X Y:Herit Q) (A B:Fin (a+1)→ℝ) (Z y δ)(o:CellR), R.anchor ≤ m→ m ≤ i → i<b → b≤ N → b≤ M →Compar R.draws.S R.y m (i+1)≤ Z → Bough Q F y Z B →δWarm R i b≤ δ → Sitting Q A e δ X Y →
   let V' k:=paceT R.draws.S m k; Fringed (capP Q) e u (V' i) (C.buy Z*(V' i^d)*(∏ i,B i*A i)) δ (Ash R.draws R.paid F X m i N y o) (Ash R.draws R.paid F Y m i M y o):=by
   let k:=capP Q; let t:= u+(k+d)
   obtain ⟨c,hc⟩:= moth Finset.univ (fun l=> (hardCash e u E W V H (Q l)).plus (hardCash e t E W V H (Q l)))
   let κ:=(coinMat k e+1)^a; let RPrice:= priceWG G e k u (k+d) E W'; let f:= E.powC k; let τ:Credit:= (pur 48).prodC Credit.leanC
   let L:=((((((pur (a:ℝ)).prodC RPrice).prodC (Credit.leanC.powC (k+d))).prodC (τ.powC u)).prodC (pur κ)).prodC f).prodC (c.powC (a+1))
   refine ⟨L,fun R H' p m i b N M F X Y A B Z y δ o hm hi ht hn hM hz q v l=>?_⟩; intro V'
   let P:= ll R.draws i; let I:= R.draws.S; let x:= V' (i+1); let η:=V' i; have hx:0<x:= pace_pos ..; have he:0<η:= pace_pos ..; have hR:R.tempC (i+1) b ≤ δ:= (R.also_temp (hm.trans hi)).trans v; have hη:η≤1:=pace_le _ hi
   have hδ:0≤δ:= (trail_pos ..).le.trans hR; let X' n U:= Ash R.draws R.paid F U m i n y o; let L':= c.buy Z
   let B' j:= L'*(x^(asp Q j))⁻¹ * (B j*A j); let C n d:= awaken Q R.draws R.paid F d m (i+1) n y o; let S j:=VisitsT (F j) x y o
   let c':ℝ:= P.L.val; have hc':0< c':=by unfold c'; positivity
   let R' j:= saddleP P.L (S j); have hX: x*c'=η:=pace_step ..; let T:=∏ i,B i*A i
   have μ j:0 ≤ B j*A j:= mul_nonneg (q.lanes j).1 (l.stock j); have hT:= Finset.prod_nonneg (s:=Finset.univ) (fun i _=> μ i)
   by_cases hp:∀ i,(S i).Nonempty; swap; · obtain ⟨g,hg⟩:=not_forall.mp hp; have hk Z (d') (h':i<Z): X' Z d'=0:= deltaZero (C Z d') g (vacant _ _ F o g hg d') _ R.green h' R.hG (asp Q); change Fringed k e u η (L.buy Z*η^d*T) δ (X' N X) (X' M Y); rw [hk N X (ht.trans_le hn),hk M Y (ht.trans_le hM)]; exact Fringed.nullV hδ (mul_nonneg (mul_nonneg (zero_le_one.trans (L.purchase q.pos)) (pow_nonneg he.le _)) hT)
   have hw n p: n≠p→ SplitHill (R' n) (R' p) η (4*(3*Z)) (Z⁻¹/η):=by
      intro h; rw [←hX]; apply disjointly P _ _ _ _ _ (3*Z) o hx (hX ▸ hη) (q.seats n p h) (inv_pos.mpr (zero_lt_one.trans_le q.pos)) ?_ ?_ (hp _) (hp _)
      · exact hX ▸ roads _ (q.rents n) q.room he hη
      exact hX ▸ roads _ (q.rents p) q.room he hη
   have hZ := q.pos; have hv:0< Z:= zero_lt_one.trans_le q.pos; have hj:= lt_of_lt_of_le ht hn; have hh:=lt_of_lt_of_le ht hM
   let hP j:PassportC H R (Q j) W V:= Classical.choice (H' j)
   have ha j:Auth (asp Q j) (C N X j):= locale_val _ (passportHead (hP j) (F j) _ _ (by omega) hj) _
   have hb j:Auth (asp Q j) (C M Y j):= locale_val _ (passportHead (hP j) (F j) _ _ (by omega) hh) _
   have hy j: PaidMer e t (heirP R.draws i (R' j)) (C N X j) (C M Y j) (B' j) δ:=by
     have h:= (capLife (hP j) hm (show m≤ i+1 by omega) ht hn hM hz (l.stock j) hR (X j) (Y j) (l.track j) (F j) (q.rents j) t o q.room (q.lanes j)).2 P; intro k r v; have hz: (hardCash e t E W V H (Q j)).buy Z≤ L':= (Credit.thickened _ hZ).trans (hc j (Finset.mem_univ _) _ hZ)
     exact (h k r v).stepX (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hz (show 0≤ (x^(asp Q j))⁻¹ by positivity)) (μ j)) hδ
   have hco j: Fringed (asp Q j) e u η (B' j) δ (verseI R.draws R.paid i N (asp Q j) (C N X j)) (verseI R.draws R.paid i M (asp Q j) (C M Y j)):=by
      change Fringed _ _ _ _ _ _ (verseI _ _ _ _ _ (locale _ ((Q j).spins _ _ _ _ _ _ _ _))) (verseI _ _ _ _ _ (locale _ ((Q j).spins _ _ _ _ _ _ _ _))); have hu:=passportCarry (y:=y) (hP j) (F j) (X j) o hm hi hj; have he':=passportCarry (y:=y) (hP j) (F j) (Y j) o hm hi hh
      rw [hu,he']; have hy':Compar I R.y m i ≤ Z := ((compar_age I R.y m) (Nat.le_succ i)).trans hz; have hv: R.tempC i b≤δ:= (PathCost.narrow I (Nat.le_succ i) b).trans hR; apply (capLife (hP j) hm hi ht.le hn hM hy' (l.stock j) hv (X j) (Y j) (l.track j) (F j) (q.rents j) u o q.room (q.lanes j)).1.pay; unfold B'; apply mul_le_mul_of_nonneg_right _ (μ j); have hv: x≤ η:=by rw [←hX]; exact le_mul_of_one_le_right hx.le (Nat.one_le_cast.mpr P.L.pos)
      exact mul_le_mul ((Credit.thickens _ hZ).trans (hc j (Finset.mem_univ _) _ hZ)) (inv_anti₀ (pow_pos hx _) (pow_le_pow_left₀ hx.le hv _)) (show 0 ≤ (η^(asp Q j))⁻¹ by positivity) (zero_le_one.trans (c.purchase hZ))
   apply (drifted a (C N X) (C M Y) (asp Q) B' R' (by linarith only [hZ]) (div_pos (inv_pos.mpr hv) he) (le_refl k) he.le hw p (hm.trans hi) ht hn hM v ha hb hy hco).pay
   have hτ : 48*Z ≤ τ.buy Z:=by unfold τ; rw [Credit.products, Credit.lean_cost]; exact mul_le_mul_of_nonneg_right (pure_goal ..) hv.le
   let Ld:= τ.buy Z^u; have hf₁:0≤ κ:= pow_nonneg (by linarith [coinMat_nn k e]) _; have hf₂:0≤ Ld:= pow_nonneg (zero_le_one.trans (τ.purchase hZ)) _; have h'':0≤ L':= zero_le_one.trans (c.purchase hZ); have hf₃:0≤ L'^(a+1):= by positivity
   have hd: R.y i ≤ Z := by
      let q':= PadRank.frugal R hm (show m≤ i+1 by omega)
      exact (q'.year _ hi (Nat.le_succ i)).trans hz
   have hj':R.cash RPrice i ≤ RPrice.buy Z := RPrice.elder (R.depth _ (hm.trans hi)) hd; have hX': c' ≤ E.buy Z := ((R.taxes i (hm.trans hi)).height).trans (E.elder (R.depth _ (hm.trans hi)) hd)
   have ht' : pearlB u (k+d) (4*(3*Z)) (Z⁻¹/η) ≤ (Z^(k+d)*(η^(k+d))*Ld):=by
       unfold pearlB; rw [←inv_pow (Z⁻¹ / η)]
       have hv: (Z⁻¹ / η)⁻¹=Z*η:=by field_simp
       rw [hv,mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity)
   have hl: (∏ i,B' i)= L'^(a+1)*(η^k)⁻¹*c'^k*T:=by rw [show (∏ i,B' i)= _ from costs_join L' x (fun i=>B i*A i) (asp Q)]; rw [← hX,mul_pow]; unfold T k capP; field_simp
   rw [loadRep,hl]; change _*R.cash RPrice i* _* (κ * (L'^(a+1) * _*c'^k*T))≤ (L.buy Z*η^d*T)
   let C':= (pur (a:ℝ)).buy Z; let T':=L'^(a+1)*(η^k)⁻¹; have hv:0≤ T':=by unfold T'; positivity
   have hv': T'*c'^k *T≤ T'*(E.buy Z)^k *T:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc'.le hX' k) hv) hT
   have hr':0≤RPrice.buy Z:=zero_le_one.trans (RPrice.purchase hZ); have hC':0≤ C':=(by exact le_trans (by positivity) (pure_goal ..))
   apply (show _≤ C'*RPrice.buy Z*(Z^(k+d)*η^(k+d)*Ld)*(κ*(T'*(E.buy Z)^k*T)) from mul_le_mul (mul_le_mul (mul_le_mul (pure_goal ..) hj' (zero_le_one.trans (RPrice.purchase (R.depth _ (hm.trans hi)))) hC') ht' (by unfold pearlB; positivity) (mul_nonneg hC' hr')) (mul_le_mul_of_nonneg_left hv' hf₁) (by refine mul_nonneg hf₁ (mul_nonneg (mul_nonneg hv (by positivity)) hT)) (mul_nonneg (mul_nonneg hC' hr') (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hf₂))).trans
   refine le_of_eq ?_; unfold L; simp only [Credit.products,Credit.power,f,Credit.lean_cost]; unfold T' Ld C' L'; rw [show (pur κ).buy Z=κ from ?_]; rw [pow_add η]; field_simp
   have hc:1≤ coinMat k e+1:=by linarith [coinMat_nn k e]
   unfold pur Credit.buy κ; simp [max_eq_right (one_le_pow₀ hc)]
end YM.WilsonCoeffUV.Mer

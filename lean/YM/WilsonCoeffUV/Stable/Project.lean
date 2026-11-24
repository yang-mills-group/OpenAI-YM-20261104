import YM.WilsonCoeffUV.Stable.Split
/-!
# Local deterministic rate and π lease
-/
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c L:Side}{U V:Type*}{r h D l j e k a m u N:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B δ:ℝ}
lemma arret_billP (c:Volume D)(P:ChamberTen G (Vote D) r)(h l:ℕ)(p:Fruit 0 1 u P A)(hp:h*l≤u): SumBudget (fun i=>‖(P i c) • skyline h i l‖) ((Fountain.tune G h r l).choose*‖c‖*A):=by
    let V:=(Fountain.tune G h r l).choose; have hv:0≤V:= (Fountain.tune ..).choose_spec.1
    refine budget_minor (cap_scale (p.slice zero_le_one hp) (show 0≤V*‖c‖ by positivity)) (fun _=>norm_nonneg _) (fun i=>?_)
    rw [norm_smul]; unfold hedge autumn; rw [one_mul]; exact (mul_le_mul ((P i).le_opNorm c) ((Fountain.tune ..).choose_spec.2 i) (norm_nonneg _) (by positivity)).trans_eq (by rw [show tread Bank.terrain 0 i= port_d 0 i from rfl]; ring)
lemma echo_credit (F:Frame G h)(p:h*h≤u)(r D): ∃ C:ℝ,0≤ C ∧ ∀ i:Alma F,∀ (Y:ChamberTen G (Vote D) r)(A:ℝ),Fruit 0 1 u Y A→ ‖echoS F Y i‖≤ C*A:=by
   let V i:= (Fountain.tune G h r (valence F i)).choose*‖brow F i D‖; let K i:= ‖Bell F (weave F i) (valence F i)‖*V i; let C:= ∑ i,|K i|
   have he i: K i ≤ C:= (le_abs_self _).trans (Finset.single_le_sum (fun i _=> abs_nonneg (K i)) (Finset.mem_univ i)); refine ⟨C,Finset.sum_nonneg fun _ _=> abs_nonneg _,fun i Y A q=>?_⟩
   have hk:= arret_billP (brow F i D) Y h (valence F i) q ((Nat.mul_le_mul_left h (valence_cap ..)).trans p)
   have hv := le_trans (Complex.abs_re_le_norm (trellis F Y i)) (norm_le_pi_norm (Bell F (weave F i) (valence F i) (arret (brow F i D) Y h (valence F i))) (sheet F i)); refine hv.trans (((Bell F _ _).le_opNorm _).trans ?_);
   exact (mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hk.2.1).trans hk.2.2) (norm_nonneg _)).trans ((le_of_eq (mul_assoc ..).symm).trans (mul_le_mul_of_nonneg_right (he i) q.C))
lemma echoLP (F:Frame G h)(i:Alma F){P Q:ChamberTen G (Vote D) r}(p:Fruit 0 1 u P A)(q:Fruit 0 1 u Q B)(hv:h*h≤u) : echoS F (P-Q) i= echoS F P i- echoS F Q i:=by
    let v:=brow F i D; let T:=valence F i; have hx:h*T≤u:= (Nat.mul_le_mul_left _ (valence_cap ..)).trans hv
    have hp: arret v (P-Q) h T=arret v P h T-arret v Q h T:=by unfold arret; simp_rw [Pi.sub_apply, _root_.sub_apply, sub_smul]; exact ((arret_billP v P h T p hx).2.1.of_norm.tsum_sub (arret_billP v Q h T q hx).2.1.of_norm)
    unfold echoS trellis; rw [hp,map_sub]; rfl
lemma echoLP_add (F:Frame G h)(i:Alma F){P Q:ChamberTen G (Vote D) r}(p:Fruit 0 1 u P A)(q:Fruit 0 1 u Q B)(hv:h*h≤u) : echoS F (P+Q) i= echoS F P i+ echoS F Q i:=by
    have ht:= echoLP F i (p.plus q zero_le_one) q hv; rw [add_sub_cancel_right] at ht; exact eq_add_of_sub_eq ht.symm
lemma echoSupport (F:Frame G h)(h:h*h≤u)(P Q:ChamberTen G (Vote D) r)(p:YieldP 0 1 u A δ P Q)(i:Alma F): twain ((echo_credit F h r D).choose*A) δ (echoS F P i) (echoS F Q i):=by
    have he:=(echo_credit F h r D).choose_spec.2; refine ⟨he i P A p.wax,he i Q A p.wane,?_⟩; rw [← echoLP F i p.wax p.wane h, mul_assoc]; exact he i _ _ p.toll
lemma pTax_fixed (F:Frame G h)(Y:Single G D)(hp:h*h≤u)(j:Alma F)(p:∀i<e,∀k<valence F j,Fruit 0 1 u (Y i k) A)(ha:0 ≤A): ‖ptax F Y e j‖≤(∑ k∈Finset.range (valence F j),(echo_credit F hp k D).choose)*A:=by
    apply (norm_sum_le ..).trans; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun k hk=>?_ ; have he:= Finset.mem_range.mp hk; split; · exact (echo_credit F hp k D).choose_spec.2 j _ A (p _ (by omega) _ he)
    rw [norm_zero]; exact mul_nonneg (echo_credit F hp k D).choose_spec.1 ha
lemma hear_input (F: Frame G h)(q:h*h≤u)(Y:Single G D)(A:ℝ)(hA:0≤A)(H:∀ i<e,∀ j<r,Fruit 0 1 u (Y i j) A)(hp:∀ i:Alma F, valence F i=r → glean F Y e i=0): Hears F h ((∑ k∈ Finset.range r,(echo_credit F q k D).choose)*A) (Y e r):=by
    refine ⟨mul_nonneg (Finset.sum_nonneg fun k _=> (echo_credit F q k D).choose_spec.1) hA, fun i _ z =>?_⟩
    have he:= hp i z; rw [tail_glint] at he; rw [←z, show echoS F (Y e (valence F i)) i = -(ptax F Y e i) from eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact he), norm_neg]; exact pTax_fixed F Y q i (fun a ha r v=> H a ha _ (z ▸ v)) hA

-- Demand builder meaningful prior to beacon.
def PrivCost (F:Frame G h)(H:Hol G)(p:h<D)(u r:ℕ)(g:h+(h+1)≤u)(hp:(h+1)*r≤u)(A s:ℝ)(e:0<s):ℝ := (repeatCap F H r p A g hp e).choose
def permeability (H:Hol G)(F:Frame G h)(p:h<D)(u r:ℕ)(B:Bulb G): ℝ:= if h':h+(h+1)≤u ∧ (h+1)*r≤u then PrivCost F H p u r h'.1 h'.2 B.preD B.s B.anger else 1

lemma Hall_tower (F:Frame G h)(H:Hol G)(p:h<D)(u r:ℕ)(hg:h+(h+1)≤u)(hp:(h+1)*r≤u)(hV:h*h≤u)(I:Cloister G h)(e:ℕ): ∃ C:ℝ,0≤C∧∀ (R: Stand (inkPin I))(_:Courant I R)(Y:Single G D) (A X:ℝ),0≤ A→Stakes Y→(∀ i<e,∀ j,Fruit 0 1 u (Y i j) A)→(∀ i:Alma F,valence F i=r→ glean F Y e i=0)→dragCup Bank.terrain I.lamp.s I.lamp.path.D R.Q→Standby (Y e r)→ Fruit 0 1 u (Y e r) X →
    let B:= I.lamp; let P:= hall (inkPin I).patch h R.Q (Y e r); Fruit 0 1 u P ((permeability H F p u r B)/(inkPin I).patch.L.val * X + C*A) ∧ Hears F h (C*A) P:=by
    let B:= I.lamp; let P:= (inkPin I).patch; let L:ℝ:=P.L.val; let V:= permeability H F p u r B; let Y:=B.preD; let D':=(inkPin I).D; let s:= I.lamp.s
    let W:=zenithW G e u (r-1); have hW:0≤ W:= costW_nn ..
    let T:= ∑ k∈Finset.range r,(echo_credit F hV k D).choose; have hT:0≤T:= Finset.sum_nonneg fun i _=>(echo_credit F hV ..).choose_spec.1
    let M:=W+T
    let U':=max (Y/L) D'; have hD:D'≤ U':= le_max_right ..; have hs:0<s:= B.anger
    have hu:0≤ U':=(zero_le_one.trans (inkPin I).bill_nn).trans hD
    let C:=veilR G u s U' r; have hc:0≤C:= veilR_nn G u hs hu r
    let K:= (echo_credit F hV r D).choose; have hk:0≤ K:= (echo_credit F hV r D).choose_spec.1
    let xota:=xota I; have he:0<xota:=(inkPin I).kernel.penalty_pos
    have hv: V=(repeatCap F H r p Y hg hp hs).choose:= by unfold V permeability; rw [dif_pos (show _ from ⟨hg,hp⟩)]; rfl
    have hv':0≤ V:= hv.symm ▸ (repeatCap F H r p Y hg hp hs).choose_spec.1
    choose N hN hw using fun i:Alma F=> hall_near r H F p (show h< u from by omega) _ he I.post I.inlet I.horizon (notar F i) (weigh_cap F i)
    let R:=∑ i,N i; have hR:0≤R:= Finset.sum_nonneg fun _ _=> hN _
    let Q:=(C*M+V*M)+(K*C*M+R*M); have hM:0≤M:=by unfold M; positivity
    have hQ:C*M+V*M≤ Q:=le_add_of_nonneg_right (by positivity);
    have hL:0≤L:=by unfold L; positivity
    let O:= L^h*Q; have hO:0≤O:=mul_nonneg (by positivity) ((by positivity : 0≤ C*M+V*M).trans hQ)
    refine ⟨O,hO,fun R' g Y' A X ha u' H' hY hr h' v=>?_⟩; dsimp only [inkPin]; let B:=Y' e r; let E:=M*A
    have hE:0≤ E:=by unfold E; positivity
    let R0:=hall P h R'.M B; let Z:=hall P h R'.Q B; have hr: dragCup Bank.terrain s U' R'.Q:= hr.le hD; have hv0 : dragCup Bank.terrain s U' R'.M:= g.price.polish.le (le_max_left ..)
    obtain ⟨t,a,ht,h'⟩:= h'; have hB:=u'.pur e r
    have hhW : VectorWind 0 1 u E B:= (VectorWind.summer u'.vert u'.pur (u:=u) (e:=e) (r:=r) (fun i hi j _=> H' i hi j) zero_le_one le_rfl ha).step (mul_le_mul_of_nonneg_right (show W≤M from le_add_of_nonneg_right hT) ha)
    have htT:= hear_input F hV Y' A ha (r:=r) (e:=e) (fun i hi j _=>H' i hi j) hY; have hx : Hears F h E B:=⟨hE,fun i hi y=> (htT.tell i hi y).trans (mul_le_mul_of_nonneg_right (show T≤M from le_add_of_nonneg_left hW) ha)⟩
    have hp' : Fruit 0 1 u (Z-R0) (L^h*(C*E)):= hall_turnR P h hs hv0 hr R'.T R'.rule (dragCup.le (dragCup.mono R'.rolls (I.lamp.outlet.trans I.lamp.path.holds.le)) hD) hB (v.shave (by positivity) (show (1:ℝ)/L≤1 by rw [one_div]; exact speck_le P)) (hhW.shave (by positivity) (show (1:ℝ)/L≤1 by rw [one_div]; exact speck_le P)) zero_le_one le_rfl
    have hG : Fruit 0 1 u R0 (V/L*X+V*L^h*E):= by rw [hv]; exact (repeatCap F H r p _ hg hp hs).choose_spec.2 P R'.M B t X E a ht g.price hB (u'.m e r) h' hhW hx v
    have hh := hp'.plus hG zero_le_one; rw [sub_add_cancel] at hh
    refine ⟨hh.more ?_,mul_nonneg hO ha,fun i _ y=>?_⟩
    · rw [show L^h*(C*E)+(V/L*X+V*L^h*E)=V/L*X+L^h*(C*M+V*M)*A from by unfold E; ring]; exact add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (by positivity)) ha) _
    let b:= min t s; have hb:0<b:=lt_min ht hs; have hL : (P.L.val:ℝ)≥1:=by exact_mod_cast P.L.property
    have hw' : ‖echoS F R0 i‖ ≤ L^h*R*E:=by
        have he:= hw i g.g _ g.shape _ g.same B a t b U' E h' hb (g.Qmat ▸ (hv0.mono (min_le_right ..))) (le_trans (div_le_self hb.le hL) (min_le_left ..)) hB (u'.m e r) hhW hx
        refine le_trans ((Complex.abs_re_le_norm (trellis F R0 i)).trans (norm_le_pi_norm (Bell F (weave F i) (valence F i) (arret (brow F i D) R0 h (valence F i))) (sheet F i))) ?_
        unfold R0 P; rw [y,g.Qmat]; apply he.trans; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _=>hN i) (Finset.mem_univ i)) (by positivity)) hE
    have hy:‖echoS F (Z-R0) i‖≤ K*(L^h*(C*E)):= (echo_credit F hV r D).choose_spec.2 i _ _ hp'
    change ‖echoS F Z i‖ ≤ O*A; rw [show echoS F Z i= echoS F (Z-R0) i + echoS F R0 i from by rw [echoLP F i hh hG hV, sub_add_cancel]]
    refine (norm_add_le ..).trans ((add_le_add hy hw').trans ?_); rw [show K*(L^h*(C*E))+L^h*R*E=L^h*(K*C*M+R*M)*A from by unfold E; ring]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show K*C*M+R*M≤Q from le_add_of_nonneg_left (by positivity)) (by positivity)) ha
end YM.WilsonCoeffUV.Shard

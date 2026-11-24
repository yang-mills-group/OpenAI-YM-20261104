import YM.WilsonCoeffUV.Wick.Gauge
import YM.WilsonCoeffUV.Root.UV.Names
/-!
# Exact carry on through slots in declared projection (Wick)
GS.rates next. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm Fountain
open Bank.Carp
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {c f n:Side}{U V α:Type*} {G:Gauge} {h D i j k e n' m N r:ℕ}{F:Labels.Frame G h} {H:Hol G}
variable {z ξ σ A' B:ℝ} {s t:ℝ}
lemma HiddenK {P:ChamberTen G (Vote D) (r+1)}(p:Wing 0 0 0 P) (x:Cover)(i:G.ColorIndex): windsL x i P=0:=by
    let Z: roaring 0 P 0 0:=p
    funext j; exact norm_le_zero_iff.mp ((Z.2 x i).2 j |>.trans_eq (zero_mul ..))
lemma Hedged.affix {P Q: Ten (Vote D) (YForest G) r}(p:Hedged P)(q:Hedged Q): Hedged (P-Q):=by
    refine ⟨?_,?_,by simpa only [show (-1:ℝ) • Q= -Q from neg_one_smul ℝ Q, sub_eq_add_neg] using p.tax.mix (q.tax.μ (-1)),?_⟩
    · intro v t i; simp only [Pi.sub_apply,smul_sub,Finset.sum_sub_distrib]; rw [p.mossP v t i,q.mossP v t i]
    · intro v t; simp only [Pi.sub_apply]; rw [p.sheen v,q.sheen v]
    intro s; cases r with
    | zero=> exact le_rfl
    | succ r=>
       refine (show roaring 0 (P-Q) s 0 from ⟨le_rfl,fun x i=>?_⟩); have hx : windsL x i (P-Q)=0:=by
          rw [show windsL x i (P-Q)=windsL x i P-windsL x i Q from ?_,HiddenK (p.emits 0),HiddenK (q.emits 0),sub_self]; funext y; simp only [windsL,Finset.sum_apply,Pi.sub_apply, prune,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; abel
       rw [hx]; exact Prance.zero
-- may use only narrow post widths for pose eq. explicit frame & stipend.
lemma identify_pose (F:Frame G h)(H:Hol G)(I:Cloister G h)(Q:Stand (inkPin I))(T:Courant I Q)(p:h<D)(e:0<s)(g:dragCup Bank.terrain s B Q.Q)(P:ChamberTen G (Vote D) r)(hp:Hedged P)(u:Hears F h 0 P):
    Hears F h 0 (hall (inkPin I).patch h Q.Q P):=by
    let A:=(inkPin I); let L:=A.patch; obtain ⟨s',C,hc,h'⟩:= hp.tax; let X:=min s (min s' I.lamp.s); have hx:0<X:= lt_min e (lt_min hc I.lamp.anger)
    have he:X≤I.lamp.s:= (min_le_right ..).trans (min_le_right ..); have hL:X/L.L.val≤ s':=(div_le_self hx.le (by exact_mod_cast L.L.property)).trans ((min_le_right ..).trans (min_le_left ..))
    let b:=max A.D (max (I.lamp.preD/L.L.val) B); let J:=hall L h Q.M P
    have hv : dragCup Bank.terrain X b Q.M:= ((T.price.polish).mono he).le ((le_max_left (I.lamp.preD/L.L.val) B).trans (le_max_right ..))
    have hh: hall A.patch h Q.Q P=hall A.patch h Q.M P:= by
       have hU:= hall_cross A.patch Q.Q Q.M P h hp.sheen h' (hp.emits s') Q.T Q.rule ((Q.rolls.mono (he.trans (I.lamp.outlet.trans A.holds.le))).le (le_max_left A.D (max _ _))) (dragCup.le (g.mono (min_le_left ..)) ((le_max_right _ B).trans (le_max_right A.D _))) hv hL (half_pos hx).le (half_lt_self hx)
       rw [mul_zero,mul_zero] at hU; exact sub_eq_zero.mp (wing0 hU)
    rw [hh]; refine ⟨le_rfl,fun i _ q=>?_⟩
    let W:=weave F i
    obtain ⟨V,hV,H⟩:= hall_dear r H F p (k:=0) (Nat.zero_le h) (xota I) A.kernel.penalty_pos I.post I.inlet I.horizon (notar F i) (a:=weave F i) (weigh_cap F i) s' hc
    have hR:= H T.g L T.shape _ T.same P C X b 0 h' hx (show dragCup Bank.terrain _ _ (Agate L T.line G) from T.Qmat ▸ hv) hL hp.sheen hp.mossP (hp.emits s') (fun _=>hp.emits s') (fun _ h=> by omega) u J (by unfold J; rw [T.Qmat]) (hall_grace A.patch _ _ h hp.sheen)
    apply le_trans (le_trans (Complex.abs_re_le_norm _) (norm_le_pi_norm (Bell F (weave F i) (valence F i) (arret (brow F i D) J h (valence F i))) (sheet F i))); rw [q]; exact hR.trans_eq (mul_zero ..)

lemma Hedged.plus {P Q:ChamberTen G (Vote D) r}(p:Hedged P)(q:Hedged Q): Hedged (P+Q):=by
    refine ⟨?_,p.sheen.add q.sheen,p.tax.mix q.tax,?_⟩
    · intro v t i; simp only [Pi.add_apply,smul_add,Finset.sum_add_distrib]; rw [p.mossP v t i,q.mossP v t i]
    intro s; cases r with
    | zero=> exact le_rfl
    | succ r=>
        refine (show roaring 0 (P+Q) s 0 from ⟨le_rfl,fun x i=>?_⟩); have hx:windsL x i (P+Q)=0:=by rw [show windsL x i (P+Q)= windsL x i P+windsL x i Q from ?_, HiddenK (p.emits 0), HiddenK (q.emits 0),add_zero]; funext y; simp only [windsL,Finset.sum_apply, Pi.add_apply,Pi.sub_apply,prune,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; abel
        rw [hx]; exact Prance.zero
lemma Hedged.nil : Hedged (0:ChamberTen G (Vote D) r):=by
    refine ⟨fun v t i=>by simp, Smooth.zero, Standby.zero,?_⟩
    intro x; cases r with
    | zero=> exact le_rfl
    | succ r=> refine ⟨le_rfl,fun v i=>?_⟩; rw [show windsL v i (0:ChamberTen G (Vote D) (r+1))=0 from funext (fun i=>by simp [windsL,prune])]; exact Prance.zero
lemma Hedged.pooled (S:Finset U){P:U→ChamberTen G (Vote D) r}(p:∀ i∈S,Hedged (P i)): Hedged (∑ i∈ S,P i):=by
    classical
    induction S using Finset.induction_on with | empty=> simp only [Finset.sum_empty]; exact Hedged.nil | insert a b c ih=> rw [Finset.sum_insert c]; exact Hedged.plus (p _ (Finset.mem_insert_self ..)) (ih fun i v=>p i (Finset.mem_insert_of_mem v))
lemma Hedged.loom {P:ChamberTen G (Vote D) r}(p:Hedged P)(a:ℝ): Hedged (a•P):=by
    refine ⟨?_,p.sheen.smul _,p.tax.μ a,?_⟩
    · intro y j t; rw [Pi.smul_apply,p.mossP y,Finset.smul_sum]; simp_rw [Pi.smul_apply]; exact Finset.sum_congr rfl fun _ _=>smul_comm ..
    intro s; cases r with
    | zero=> exact le_rfl
    | succ r=> refine ⟨le_rfl,fun x i=>?_⟩; rw [windsCast x i a P,HiddenK (p.emits 0),smul_zero]; exact Prance.zero

lemma visibleN {j:Alma F} {P Q:ChamberTen G (Vote D) (valence F j)}(p:Hedged P)(q:Hedged Q)(I:Cloister G h)(T:Stand (inkPin I))(R:Courant I T)(g:Hears F h 0 (P-Q))(hq:h<D)(H:Hol G)(v:dragCup Bank.terrain s A' T.Q)(ht:0<s): echoS F (hall (inkPin I).patch h T.Q P) j=echoS F (hall (inkPin I).patch h T.Q Q) j:=by
    let A:=(inkPin I).patch; have H':=identify_pose F H I T R hq ht v _ (Hedged.affix p q) g; have hh:=H'.tell
    have he:echoS F (hall A h T.Q (P-Q)) j=0:=norm_le_zero_iff.mp (hh j (weigh_cap ..) rfl)
    obtain ⟨u,X,hX,hZ⟩:= p.tax; obtain ⟨y,Y,hY,hv⟩:= q.tax; let m:= min u y; have h₀:0<m:=lt_min hX hY
    let s':= min m s; have hs:0<s':=lt_min h₀ ht; have hp:s'/A.L.val≤ m:= (div_le_self hs.le (by exact_mod_cast A.L.property)).trans (min_le_left ..)
    let W:=v.mono (show s'≤s from min_le_right ..)
    let B:= max X Y; have hu:Twig 0 m B P :=Cork.cost (Cork.mono hZ (min_le_left ..)) (le_max_left ..)
    have ht:Twig 0 m B Q:= Cork.cost (Cork.mono hv (min_le_right ..)) (le_max_right ..)
    rw [hall_diff A T.Q W P Q hu ht hs hp, echo_minus F _ (hall_fares _ _ W _ _ hu hp (half_pos hs).le (half_lt_self hs)) (hall_fares _ _ W _ _ ht hp (half_pos hs).le (half_lt_self hs)) (half_pos hs) (half_pos hs)] at he; exact sub_eq_zero.mp he
end YM.WilsonCoeffUV.Cosmos

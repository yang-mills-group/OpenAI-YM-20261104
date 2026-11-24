import YM.SignedWilsonExpansion.F9.Pulse
import YM.WilsonCoeffUV.Product.I.Charge
/-!
# Mer point rank recurrence (length bill)

Work in precisely the (history-dependent) conditional kernel of F9. Charge
all departures from rank diagonal using the bought FULL formal Recursion
clock, not a kinetic/quadratic-only splice. Angular width dependence shown
with polynomial pre/post split. No Wick gauge equivalence necessary. Rank-zero
probe is not removed.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{h D p k m N t u e i j l r:ℕ}{F:Labels.Frame G h}
variable {a x s s' b c B M X:ℝ}

lemma attends {Y:Era G ℝ} (hu:Auth k Y)(e r u:ℕ): ∃ B:ℝ,Fruit 0 1 u (Y.2 e r) B:=by
    obtain ⟨s,t,h,H⟩:= (hu.wing e r).land; exact ⟨_,twig_lp H h u⟩
-- charge every predecessor, including not yet used lower powers.
def Earlier (Y:Era G ℝ)(e r u:ℕ)(M:ℝ):Prop:=∀ i j,lowerGrade i j e r→ Fruit 0 1 u (Y.2 i j) M
lemma delta_price (k e r u:ℕ)(G:Gauge) : ∃ d:ℕ,∀ h:ℕ,∀ I:Cloister G h,∃ C:ℝ,0≤ C∧∀ (S:Rally (e+1) 0 (inkPin I))(P:Courant I S.P)(Y:Era G ℝ)(M:ℝ),
    Auth k Y→0≤ M→Earlier Y e r u M→
    Fruit 0 1 u (sunI (inkPin I) S.P k Y.2 e r-pump (Y.2 e r) (owns _ S.P.M)) (C*S.x^d*M):=by
    obtain ⟨d,H⟩:= spursDue G k e r u
    refine ⟨d,fun h I=>?_⟩; obtain ⟨C,a,f⟩:= H (inkPin I); let J:= (inkPin I); let L:=J.patch.L; let B:= I.lamp.preD/L.val; let s:=I.lamp.s; let R:=B+J.D; let V:=veilR G u s R r; let Z:=zenithW G e u (r-1)
    have hs:= I.lamp.anger; have hX:= I.lamp.dept; have he:0≤B:=by unfold B; positivity
    have hr:0≤R:= he.trans (le_add_of_nonneg_right (zero_le_one.trans J.bill_nn)); have hu:0≤V:= veilR_nn _ _ hs hr r; have hz:0≤Z:= costW_nn ..
    refine ⟨C+V*Z,by positivity,fun S P Y M hY hm p=>?_⟩; let t:= (1:ℝ)/L.val; have ht: 0≤t:=by unfold t; positivity
    have ht': t≤1:=div_le_self zero_le_one (by exact_mod_cast L.pos)
    let Q:= Y.2 e r; let T:= S.P
    obtain ⟨A',hf⟩:= attends hY e r u; have hf (w:Site L) (hx:w=0) : Fruit (L.val • (0:Cover)+lift w) t u Q A':=by rw [smul_zero, hx,coat0,add_zero]; exact hf.shave ht ht'
    let Y': DriftR J e r u:=⟨S,Y.2,Y.2,1,zero_le_one,le_rfl,M,hm,fun i j z=>YieldP.same ((p i j z).shave ht ht') S.θ⟩
    have hv: Fruit 0 1 u (spinCo J S.P k e r Y.2) (C*S.x^d*M):= (f Y').wax
    rw [sunshineW]
    have hp:VectorWind 0 t u (Z*M) Q:= VectorWind.summer hY.roots hY.coverP (fun i h j _=>((Y'.h i j (Or.inl h)).wax)) ht ht' hm
    have hy: J.D ≤ R:= le_add_of_nonneg_left he
    have hQ: Fruit 0 1 u (pump Q (owns L T.Q)-pump Q (owns L T.M)) (V*(Z*M)):= itR (K:=T.M) (w:=0) (hf 0 rfl) (P.price.polish.le (le_add_of_nonneg_right (zero_le_one.trans J.bill_nn))) ((S.Υ.mono (I.lamp.outlet.trans I.lamp.path.holds.le)).oneP.le hy) (hY.coverP e r) T.rule (by rw [smul_zero,coat0,add_zero]; exact hp) ((T.rolls.mono (I.lamp.outlet.trans I.lamp.path.holds.le)).le hy) hs zero_le_one le_rfl
    rw [add_sub_right_comm]; apply (hQ.plus hv zero_le_one).more; rw [add_mul,add_mul,add_comm _ (V*Z*S.x^d*M),←mul_assoc]; exact add_le_add_left (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) (one_le_pow₀ S.rich)) hm) _
-- pre-length constants; recover with no previous-scale volume
abbrev backL (D:ℕ):ℝ:= ‖out D‖
lemma backL_nn (D:ℕ):0≤backL D:= norm_nonneg (out D)
structure Ample (h u r:ℕ):Prop where
    all:h+(h+1)≤u
    ranks:(h+1)*r≤u
    floor:h*h≤u
def peak (H:Hol G)(F:Frame G h)(u r:ℕ)(Ra:Ample h u r)(x s:ℝ)(hp:0<s):=
    (pulse_gain F H u r (Nat.lt_succ_self _) x hp Ra.all Ra.ranks).choose
-- engineer supplies at-sale price in Cloister
lemma pump_gain (H:Hol G)(F:Frame G h)(u r e:ℕ)(Ra:Ample h u r)(L:Cloister G h): ∃ W:ℝ,0≤ W ∧ ∀ (S:Stand (inkPin L))(P:Courant L S)
    (Y: Era G ℝ)(k)(A' M:ℝ), Auth k Y→0≤ M→Earlier Y e r u M→(∀ i:TagIx F r,row F (Y.2 e r) i=0)→Fruit 0 1 u (Y.2 e r) A' →
    let I:= L.lamp; let B:= peak H F u r Ra I.preD I.s I.anger; let d:=h+1; let R:=I.path.patch
    Fruit 0 1 u (pump (Y.2 e r) (owns R.L S.M)) ((backL d * B * coinL d)* speck R^d*A'+ W*M) ∧ ∀ i:TagIx F r,
      ‖row F (pump (Y.2 e r) (owns R.L S.M)) i‖ ≤ W*M:=by
    let T:= L.lamp; let R:= T.path.patch; let t:=T.s; let H':=T.preD
    have ht:0<t:=T.anger; let b:= h+1; let A:=peak H F u r Ra H' t ht; let V:= zenithW G e u (r-1)
    let C:= A*V*coinL b *backL b
    have hA:0≤ A:= (pulse_gain F H u r (D:=b) (Nat.lt_succ_self _) H' ht Ra.all Ra.ranks).choose_spec.1; have hV:0≤V:=costW_nn ..; have hc:0≤C:= mul_nonneg (mul_nonneg (mul_nonneg hA hV) (coinL_nn _)) (backL_nn _)
    have hz:h<u:=by have H:=Ra.all; omega
    choose D' hD h' using fun i:TagIx F r=> nearAll r H F (D:=b) (Nat.lt_succ_self _) hz (xota L) (inkPin L).kernel.penalty_pos L.post L.inlet L.horizon (notar F (seat F i)) (weigh_cap ..)
    let D:=∑ i,D' i; have hd:0≤D:= Finset.sum_nonneg (fun i _=>hD i); let W:=D*V*coinL b; have hw:0≤W:= mul_nonneg (mul_nonneg hd hV) (coinL_nn _)
    refine ⟨C+W,add_nonneg hc hw,fun S P Y k A' M hQ hm hY z p=>?_⟩; intro I B' _ _; let Q:=Y.2 e r; let Z':=S.M; let Y':= tuftV (wire b) Y; let Z:= wire b ∘ Q; let F':=V*(coinL b*M); let U:=pump Q (owns R.L Z'); let M':= T.preD/(R.L.val:ℝ); let G':= pulseS R 0 Z' Z
    have hE: Stakes Y'.2:= stakes Y hQ b; have hv: VectorWind 0 1 u F' Z:= VectorWind.summer hE.vert hE.pur (fun i h j _=>paid (Y.2 i j) (hY i j (Or.inl h)) zero_le_one b) zero_le_one le_rfl (mul_nonneg (coinL_nn _) hm)
    have hf:= paid Q p zero_le_one b; have hW:= mul_nonneg hV (mul_nonneg (coinL_nn b) hm)
    have hy:Hears F h F' Z:= hears F Q (fun i _=>by rw [z,norm_zero]; exact hW) hW
    have ht':0≤ (1:ℝ)/R.L.val:=by positivity
    obtain ⟨s,t0,hs,hb⟩:= ((hQ.tuft (wire b)).wing e r).land; have hZ := (pulse_gain F H u r (Nat.lt_succ_self _) _ ht Ra.all Ra.ranks).choose_spec.2 R 0 Z' Z s _ _ _ hs P.price (hE.pur e r) (hE.m e r) hb hv hy hf
    have hx:G'=wire b ∘ U:= focus R S.M b Q (p.shave ht' (div_le_self zero_le_one (by exact_mod_cast R.L.pos))) ht P.price.polish
    constructor
    · change Fruit 0 1 u G' (A*(speck R^b*(coinL b*A')+F')) at hZ; rw [hx] at hZ; refine (extract _ hZ zero_le_one).more ?_
      change backL b*(A*_) ≤ backL b * A * coinL b * speck R^b * A'+(C+W)*M; rw [add_mul C,← add_assoc]; exact le_add_of_le_of_nonneg (le_of_eq (by unfold F' C; ring)) (mul_nonneg hw hm)
    intro i; let τ:= min s t; let θ:=τ/2; have hτ:0<τ:=lt_min hs ht; have hθ:0<θ:=by unfold θ; positivity
    have hS:= P.price.polish.mono (min_le_right s t); have hP: τ/R.L.val≤s:=le_trans (div_le_self hτ.le (by exact_mod_cast R.L.pos)) (min_le_left ..); have hPQ:= P.Qmat
    have he : ‖Bell F (Cosmos.weave F (seat F i)) r (arret (wallope (notar F (seat F i)).val b) G' h r)‖ ≤ D' i*F':= by
        have hz : dragCup Bank.terrain τ M' (Agate R P.line G):= hPQ ▸ hS
        have ht:= h' i P.g R 0 P.shape P.line P.same Z t0 s τ M' F' hb hτ hz hP (hE.pur e r) (hE.m e r) hv hy
        change G' = _ at hx; unfold G' Z'; rw [P.Qmat]; exact ht
    change ‖row F U i‖≤ _; unfold row; rw [← hx]; let x:= seat F i; have hh:= (Complex.abs_re_le_norm (trellis F G' x)).trans (norm_le_pi_norm (Bell F (Cosmos.weave F x) (valence F x) (arret (brow F x b) G' h (valence F x))) (sheet F x)); rw [show valence F x=r from i.property] at hh
    apply hh.trans; refine he.trans ?_; change _ ≤ (C+W)*M; unfold F'; rw [add_mul]; refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg hc hm)); exact (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=>hD i) (Finset.mem_univ i)) hW).trans_eq (by unfold W D; ring)

lemma fruit_nil {V:Type*}[NormedAddCommGroup V]{r:ℕ}{X:Ten V (YForest G) r}(hx:Fruit 0 1 u X 0): X=0:=by
   funext x; apply norm_le_zero_iff.mp; have hp:=hx.1; have hh:=(Summable.le_tsum hx.2.1 x (fun i _=>hp i)).trans hx.2.2
   exact (le_mul_of_one_le_left (norm_nonneg _) (autumn_pos zero_le_one ..)).trans hh

lemma agrees_front (k r u:ℕ){S0:Cloister G h}(S:Rally 1 0 (inkPin S0))(T:Courant S0 S.P)(Y:Era G ℝ)
    (hY:Auth k Y)(hp:∀j,r<j→Y.2 0 j=0) : sunI (inkPin S0) S.P k Y.2 0 r=pump (Y.2 0 r) (owns _ S.P.M):=by
    obtain ⟨d,D⟩:= delta_price k 0 r u G; obtain ⟨C,hC,g⟩:= D h S0; have hx: Earlier Y 0 r u 0:=by
        intro i j v; unfold lowerGrade at v; have h':i=0:=by omega
        rw [h',hp j (by omega)]; exact Fruit.zero
    have he:= g S T Y 0 hY le_rfl hx; rw [mul_zero] at he; exact sub_eq_zero.mp (fruit_nil he)

lemma through0 (H:Hol G)(F:Frame G h){L:Cloister G h}(S:Rally 1 0 (inkPin L))(P:Courant L S.P)
    (Y U:Era G ℝ)(hY:Auth k Y)(hU:Auth k U)(z:U.2=sunI (inkPin L) S.P k Y.2)(p:∀j,r<j→Y.2 0 j=0)
    (i:r≤k)(d:ℕ)(he:d≤h)(hh:∀ j:TagIx F r,(F.grades j.val).1 < d→ row F (Y.2 0 r) j=0)(v:TagIx F r)(cost:(F.grades v.val).1≤d):
     let a:=(F.grades v.val).1
     row F (U.2 0 r) v= (speck (inkPin L).patch)^a * row F (Y.2 0 r) v:=by
    intro a; let I:=inkPin L; let w:= L.lamp; let R:=I.patch; let b:=h+1; let X:=Y.2 0 r; let K:=Agate R P.line G
    have hK: K=S.P.M:=P.Qmat.symm; have hx:U.2 0 r=pump X (owns R.L K):=by rw [z,hK]; exact agrees_front k r 1 S P Y hY p
    let W0:= wire b∘ X; let W1:= wire b ∘ U.2 0 r; let l:=w.s; have h':0<l:= w.anger
    obtain ⟨A',hA⟩:= attends hY 0 r 0; have hf: Fruit 0 (1/R.L.val) 0 X A':= hA.shave (by positivity) (div_le_self zero_le_one (by exact_mod_cast R.L.pos))
    have hw:W1=pulseS R 0 K W0:= by unfold W1 W0; rw [hK,focus R _ b X hf h' P.price.polish, hx,hK]
    obtain ⟨s,Xa,hs,ht⟩:= ((hY.tuft (wire b)).wing 0 r).land; let t:= min s l; have he':0<t:= lt_min hs h'; have hr:t/R.L.val≤ s:= (div_le_self he'.le (by exact_mod_cast R.L.pos)).trans (min_le_left ..)
    let Z:= seat F v; have hE:=stakes Y hY b
    have hz: Cosmos.Slate W0 F d:=by
       intro j hj; apply hears F X ?_ le_rfl; intro i h; rw [hh i (lt_of_le_of_lt h hj), norm_zero]
    have hQ:= pulse_top H F 0 _ P.shape P.same I.kernel.penalty_pos L.inlet L.horizon (show h<b from by omega) ht (calmS hs.le _ hE r) hz he (hE.m 0 r) (hE.pur 0 r) (K:=P.line) (hK.symm ▸ (P.price.polish.mono (min_le_right s l))) he' hr (hw ▸ (stakes U hU b).m 0 r) (notar F Z) (a:= Cosmos.weave F Z) (by change a+(0:Multiset Axis).card ≤ d; simpa using cost) -- replacer
    have v':valence F Z=r:= v.property
    have hx': trellis F W1 Z=speck R^a • trellis F W0 Z:=by
        unfold trellis; rw [v',hw]
        have he': a+ (notar F Z).val.card=a:= by change a+(0:Multiset Axis).card=a; simp
        unfold W0 at hw
        have h : Cosmos.weave F Z+(notar F Z).val.card=a:= he'; rw [h] at hQ; exact congr_fun hQ (sheet F Z)
    change (trellis F W1 Z).re=_*(trellis F W0 Z).re; rw [hx',Complex.smul_re]; rfl
end YM.WilsonCoeffUV.Mer.Xa

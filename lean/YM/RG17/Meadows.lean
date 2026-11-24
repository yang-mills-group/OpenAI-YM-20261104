import YM.UniformConstruction.ReadoutCompat.TarmacMonies
import YM.RG17.Juniper
import YM.RG17.Mirror
/-! Horizon0 dual ticket. Height at calibration retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits SharpGram Trace Next.UVStress PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson
open Extra.Multi FullVolume.Sever Marker Source Overlay PhysicalNext.Repeat.Mallow Bandage MergeProof MergeProof.Accent Ribbons ManyCopies Extra.Histories Extraction Word Next.Rank Station Edition Spindle Cells
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(R:Run G){S:Table R.family.book}{f: Extraction.Order}{F: Spec.Final R.family f S}{B:Filter (ℕ×ℕ)}{L:Layout F} {D:Lenses.Mantle F B}{s:Extraction.Sequence}
    (Z:Ledger L)(fx:Flick R.family.path.levels)(W:Services R.family f S)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "ι"=> R.family.path.levels
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "Q"=> wheel R.family
local notation "a"=> R.family.S.a
local notation "δ"=> renal R.family.path.levels
local notation "η"=> near R.family.path.levels
variable {n:ℕ} (J:Fin n) (d:Fin n→ℕ) (l:ℕ) (Y m:ℝ→ℕ)
local notation "S'"=> R.family.path.levels.budget
local notation "e'"=> -(0+1/16:ℝ)/2
local notation "T"=> interval D s

-- NONE omitted at terminal physical regulator. Read early station u, not replacing any all-sector masked estimate on all configurations
open Push
variable {WLG:Bid.Worth} {rL:ℕ→ℕ} {doors} (g: Log.LogPackage R.family WLG rL doors)
open OPE.Log
include R Z fx J g
-- adapted Evidence from OPE.Prices.Circuit.funding -- keep Joined
-- costs along union exactly enough for arbitrary captions along geometry
-- no p-cost divergence; m+1=j allowed but no use here.
set_option maxHeartbeats 600000 in
lemma allocatesMeadows (h:Lookup R m)(hp: Height R.family.S home OPE.run Y (1/2)) : ∃ X:ℝ→ℕ, Height R.family.S home OPE.run X (1/2) ∧ ∃ q v : ℝ→ℝ, ValueStamp home OPE.run q ∧ RateLE home OPE.run v (-(0+1/16:ℝ)/2) ∧
   ∀ᶠ r in home,∀ N p:ℕ,∀ hj: wheel R.family r < N,∀ hk:Y r ≤ N,∀ o:Fin n→ Site (R.family.side (wheel R.family r) p), (∀ i,loops R.family (wheel R.family r) p (o i) (m r+1)=0) → Spaced (R.family.path.levels.budget (wheel R.family r)).B o →
      ∀ u:(j:Fin n)→ R.family.label (d j),(∀ j:Fin n,Spindle.paid R.family (d j) (wheel R.family r) N p (u j) ≤ H (Q r)^l)→
        let V:= Cells.center R.family.S p hk 0; (∀ i, Cells.Interior (V.chamber 0) (R.family.O N p (u i) ((R.family.S.toDepth hj.le p).embed (o i))))→ (∀ z:R.family.label 0, Cells.Interior (V.chamber 0) (R.family.O N p z 0)) →
         ∃ x:R.family.label 0, CollectionR R d 0 r N p o u (q r) (v r) (Y r) (m r) x ∧ MirrorDuty R d r N p o u (q r/2) (X r) (m r) x:=by
   let E':=g; have hh:(1/2:ℝ)<1:=by norm_num
   let A:= E'.tabs; let P:= Stock.Tabs.chosen R.family.path.levels 1 A ∘ Y; have hP:Height R.family.S home OPE.run P (1/2):= hp.stock A
   have ha(r): Stock.Tabs.opens R.family.path.levels 1 (Y r) (P r):= Stock.Tabs.opened ..
   let M:= Fintype.card (Fin n); have hm:0<M:= Fintype.card_pos_iff.mpr ⟨J⟩
   let E:= E' -- may need .toPackage
   let y:= solvency g M
   obtain ⟨χ,hχ⟩:= g.lightCuts.mother
   let b(r:ℝ)(x:Fin n):=fly R.family.path.levels (d x) (Q r)/ (H (Q r))^l
   let z(i):= ManyCopies.initial R.family.path δ η (m i) (Q i) (y (Q i)) (∏ j,b i j) M
   have hG:= goingWheel R Z fx; have hv:ValueStamp home OPE.run (fun i=>∏ j,b i j):=
       ValueStamp.prod ageLarge (fun i _=> (flyStamp ageLarge hG (d i)).div ((betaStamp ageLarge hG).pow ageLarge l))
   have hRatio : ValueStamp home OPE.run (fun i=>a (Q i)/a (m i)):=by
       let P(i:ℝ):=H (Q i); have Tq:=betaStamp ageLarge hG
       have hLookupLog:=h.log
       have h:(∀ i,0<a i):= R.family.S.a_pos
       let x(i:ℝ):=a (Q i)/a (m i); refine ⟨Eventually.of_forall (fun _=>div_pos (h _) (h _)), Wallet.absolute ageLarge 1 ?_, (Tq.pow ageLarge 11).up.of_est ?_⟩ -- "h" shadowed
       · filter_upwards [hLookupLog] with i hi; rw [Real.norm_of_nonneg (div_pos (h _) (h _)|>.le)]
         exact (div_le_one (h _)).mpr (R.family.S.strictAnti.antitone ((m i|>.le_succ).trans hi.2.le))
       filter_upwards [hLookupLog, reverseSpoke C fx Z.simple] with i hi hx; rw [inv_div,Real.norm_of_nonneg (div_pos (h _) (h _)|>.le)]
       refine (div_le_iff₀ (h _)).mpr (hi.1.2.trans ((mul_le_mul_of_nonneg_right hx (pow_nonneg (zero_le_one.trans ((ι).fits.delayed _).le) _)).trans_eq (by ring)))
   have hZ:ValueStamp home OPE.run z:= gatherStamp g ageLarge _ _ h.spine hG M (solvency_stamp g ageLarge hG hm) hv hRatio
   let e(i):=4*(1+(R.family.path.levels.params (m i)).columns)*(2*(a (m i+1)^0*(H (m i+1)*(4*(1/z i)))))
   have hs : ValueStamp home OPE.run e:=by
       have hV : ValueStamp home OPE.run (fun i=> 1+(R.family.path.levels.params (m i)).columns):=by
          have hw:(∀ i:ℝ,0≤(R.family.path.levels.params (m i)).columns):= fun i=> zero_le_one.trans ((ι).params _|>.columns_ge)
          exact ⟨Eventually.of_forall (fun i=> add_pos_of_pos_of_nonneg one_pos (hw i)), (Wallet.const ageLarge _).add ageLarge (columnsWallet g ageLarge h.spine), (ValueStamp.const ageLarge one_pos).down.invLe (Eventually.of_forall fun _=>one_pos) (Eventually.of_forall fun i=>le_add_of_nonneg_right (hw i))⟩
       have h₄:=ValueStamp.const ageLarge (by norm_num : (0:ℝ)<4); simp_rw [e,pow_zero,one_mul]; exact (h₄.mul hV).mul ((ValueStamp.const ageLarge zero_lt_two).mul ((betaStamp ageLarge (h.spine.step (ι).fits.mesh)).mul (h₄.mul ((ValueStamp.const ageLarge one_pos).div hZ))))
   let q i:=2*e i; let w i:= Real.exp (- (e')* OPE.run i); have hw:= RateIs.exp (-(e')) ageLarge; have hPaid:= shortAfford g Z.simple ageLarge hP h.spine hh (hZ.zeroCost ageLarge) 0 ((hs.zeroCost ageLarge).swap (by norm_num)) hw (by norm_num)
   let v i:=2*(stakes C (Y i) (P i)/ w i)
   refine ⟨P,hP,q,v,(ValueStamp.const ageLarge zero_lt_two).mul hs,?_,?_⟩
   · simp_rw [v,div_eq_mul_inv]; apply ((RateLE.const (2:ℝ) ageLarge).mul ((stock_price A Z.simple hp ageLarge).mul (hw.inv.pays ageLarge))).mono; try ring_nf; try simp only [le_refl]


   have hB:=briar C Z.simple E.accounting; have ht:= h.spine.step (ι|>.fits.mesh); let K i:=m i+1; have h_U:= (((height0 hB ht).power 2).add (RateIs.const ageLarge one_pos) ageLarge).mul ht.mesh
   have heLic:∀ᶠ i in home,∀ x : ℕ,m i+1 ≤ x → M ≤ rL x:= ht.grows.eventually ((eventually_ge_atTop ((eventually_atTop.mp (g.spare.eventually_ge_atTop M)).choose)).mono (fun x hx y hy=> (eventually_atTop.mp (g.spare.eventually_ge_atTop M)).choose_spec y (hx.trans hy)))
   filter_upwards [hp.mesh.overtakes (h_U.pays ageLarge) ageLarge (by norm_num),height_room hp h.spine ageLarge hh (lensScope C 0), hP.earlier hh ageLarge h.spine,hp.grows.eventually_ge_atTop (R.family.ref 0), hPaid,hZ.profit,heLic,h.log,eventually_all.mpr (fun j=> hG.grows.eventually_ge_atTop (R.family.ref (d j)))] with r hC hB hΦ hY hp hz hLic hT he N p hj hk o hE hs u hc V hf ht
   let F(j):=R.family.O N p (u j) ((R.family.S.toDepth hj.le p).embed (o j)); let W(j):=b r j
   have hY':(R.family.path.levels.budget (K r)).B^2+1 ≤ (R.family.S.toDepth (((ha r).1.trans hΦ.le).trans (Nat.le_succ _)) p).count.val:=by
       let U:= R.family.S.toDepth (((ha r).1.trans hΦ.le).trans (m r|>.le_succ)) p
       have hR:((S' (K r)).B:ℝ)^2+1 ≤ U.count.val:= le_of_mul_le_mul_right (hC.le.trans_eq ((R.family.S.embeds_scale U).symm.trans (mul_comm ..))) (R.family.S.a_pos (K r))
       exact_mod_cast hR
   have hD:0 < (H (Q r))^l:= pow_pos (zero_lt_one.trans ((ι).fits.delayed _)) _
   have hw:(∀ i,0<W i):=fun i=>div_pos (inv_pos.mpr (pow_pos (zero_lt_one.trans ((ι).fits.delayed _)) _)) hD
   have hd(i): W i * Spindle.paid R.family (d i) (Q r) N p (u i) ≤ fly (ι) (d i) (Q r):=(mul_le_mul_of_nonneg_left (hc i) (hw i).le).trans_eq (div_mul_cancel₀ _ hD.ne')
   obtain ⟨x,hA,hK,hX,hXc⟩:= ManyCopies.juniper R.family N (m r) p (Y r) (P r) J (w r) W o (ha r).1 hΦ.le hj hT.2.le d u R.makes E.system E.literal (hχ 0) Z.simple A (ha r) (hY.trans (ha r).1) he hd hw hB hE hY' hs (solvency_pos g _ hm) (solvency_le g _ hm) (short g) hT.2 (fun k _ hp=> ⟨solvency_anti g M hm Z.simple hp.le,short_affords g k⟩) (fun k hk _=>hLic k hk) F (fun _=>rfl) hf ht hz le_rfl (Real.exp_pos _) hp.1 le_rfl hp.2
   have he (Z₀: Config G (R.family.side N p)) : (∏ j:Fin n,R.family.O N p (u j) (attachV R (wheel R.family r) o N j) Z₀)= ∏ i,F i Z₀ := Finset.prod_congr rfl fun j _=>by dsimp only [attachV,F]; rw [vect C _ p N (o j) hj.le]
   refine ⟨x,⟨hA,(funext he).symm ▸ (show Cards.PaidAt R.family.S N p (Y r) (R.family.beta N p) (v r) ((fun U=> ∏ i,F i U)-R.family.O N p x 0) from ⟨hk,hK,hX⟩)⟩,?_⟩
   refine ⟨(m r|>.le_succ).trans (hT.2.le.trans hj.le),?_⟩; simp_rw [he]; rw [show q r / 2 = e r from by unfold q; ring]; exact hXc
-- deploy combining PAGED exact labels from ticket. no exterior here.
include W
variable {x:Points n}(b:ℝ→ Fin n → Cover)
lemma assuresMeadows (ho:Stands L D s) (h:Lookup R m)(hp: Height R.family.S home OPE.run Y (1/2)) : ∃ X:ℝ→ℕ, Height R.family.S home OPE.run X (1/2) ∧ ∃ q v:ℝ→ℝ, ValueStamp home OPE.run q ∧ RateLE home OPE.run v (-(0+1/16:ℝ)/2) ∧
   ∀ (x:Points n)(b:ℝ→ Fin n → Cover), x∈generic n → Tendsto (fun r=>tag (role R.family r) (b r)) (interval D s) (𝓝 x) →
    ∀ᶠ r in T,∀ᶠ p:ℕ×ℕ in L.lens,∀ w:(i:Fin n)→ R.family.label (d i), (∀ i:Fin n,Paid L r w i ≤ (R.family.path.levels.clock.hatBeta (wheel R.family r))^l)→
     let o:= wrap (R.family.side (wheel R.family r) p.2) ∘ b r; let u(i):= atRef L (d i) r p (w i);
     ∃ z:R.family.label 0,CollectionR R d 0 r p.1 p.2 o u (q r) (v r) (Y r) (m r) z ∧ MirrorDuty R d r p.1 p.2 o u (q r/2) (X r) (m r) z:=by
   obtain ⟨l',hl⟩:= (eventually_all.mpr (fun j:Fin n=> eventually_ge_atTop (1+8*(d j+1)+l))).exists
   obtain ⟨X,hX,q,v,hq,hv,hQ⟩:= allocatesMeadows R Z fx J d l' Y m g h hp
   refine ⟨X,hX,q,v,hq,hv,fun x b he hT=>?_⟩
   have ht:T ≤ home:= (homes D).comp s.cofinal; have hz:= mintages R Z fx Y m b h ht ((hp.earlier (by norm_num) ageLarge h.spine).mono fun _ h=>h.le) hT he
   have ha:∀ᶠ r in T, R.family.S.a (L.level r) ≤ r:=by
       change ∀ᶠ i:ℕ in atTop, R.family.S.a (L.level (offsetPath D s i)) ≤ offsetPath D s i
       filter_upwards [s.cofinal.eventually D.proper] with i hi
       rw [ho.match_length]; exact hi.1
   filter_upwards [hz,hQ.filter_mono ht,(turnsWheel C|>.mono_left ht).eventually_ge_atTop 1,eventually_all.mpr (fun i=> (goingWheel R Z fx).grows.eventually_ge_atTop (R.family.ref (d i))|>.filter_mono ht),eventually_all.mpr (fun i=>Z.reach.growing.eventually_ge_atTop (R.family.ref (d i))|>.filter_mono ht),ha,(reverseSpoke C fx Z.simple).filter_mono ht] with r hr hp he hU hm ha hA
   let k:=Q r; let g:=Y r
   have hY:= (OPE.Cards.largeMesh f).mono_left L.certified
   filter_upwards [(large_mesh f (g)).filter_mono L.certified,(large_mesh f (k+1)).filter_mono L.certified,(large_mesh f (L.level r)).filter_mono L.certified, (late_period hr.marsh).filter_mono L.certified,hY.eventually (near_center C g 0 R.makes), eventually_all.mpr (fun i=> hY.eventually (near_center C g (d i) R.makes))] with p hg hk hM hN hT hS w hx o u
   have h':k<p.1:=hk; have hR :1 ≤ R.family.path.levels.clock.hatBeta k:= ((ι).fits.delayed k).le
   have hw (i):Spindle.paid R.family (d i) k p.1 p.2 (u i) ≤ R.family.path.levels.clock.hatBeta k^l':=by
       have hv: a (L.level r) / a k ≤ R.family.path.levels.clock.hatBeta k^8 := (div_le_iff₀ (R.family.S.a_pos _)).mpr ((ha.trans hA).trans_eq (mul_comm ..))
       have hs:= YM.RG17.ReadoutCompat.monies (p:=p.2) R fx L W (d i) 8 l k (L.level r) (w i) (r:=r) rfl he (hm i) (hU i) h'.le hM hv (hx i)
       exact ((le_mul_of_one_le_left (paid_pos ..) (col_ge C k)).trans (show moneys C (d i) k p.1 p.2 (u i) ≤ _ from hs)).trans (pow_le_pow_right₀ hR (hl i))
   have hF:Edition.Spaced (R.family.path.levels.budget k).B o∧ ∀ i,loops C k p.2 (o i) (m r+1)=0∧ R.family.S.place (o i)= R.family.S.gridPoint k (b r i) := hN
   exact hp p.1 p.2 h' hg o (fun i=>(hF.2 i).1) hF.1 u hw (fun i => hS i hg _ _ (by rw [R.family.S.embeds_place, (hF.2 i).2]; exact (hr.fit i).le.trans (R.family.S.strictAnti.antitone (hr.first.trans (Nat.le_succ _)))) _) (fun i=> hT hg p.2 _ (by rw [latzero]; simp [(R.family.S.a_pos _).le]) _)
end YM.RG17

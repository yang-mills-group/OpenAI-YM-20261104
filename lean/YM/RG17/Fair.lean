import YM.UniformConstruction.ReadoutCompat.TarmacMonies
import YM.RG17.Paddock
/-!
# Paddock stores. Target from OPE.Prices.Circuit `funding`. Allows
 m-parent same Rate as wheel. Towed paidSupport credit from actual L,
 no switching to fixed-period PaidAt calibration. Need layout on stems basis
 to apply to Campus profile; used in Agenda for rail sensors. Unlike PriceAt
 this takes variable **same top charges**. No assertion of constructive
 *formula* identity for the returned `z`. Exact rate and
 sized surplus with ALL copies. Sufficient packing for suggested projection.
-/
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
variable {n:ℕ} (J:Fin n) (d:Fin n→ℕ) (l t:ℕ) (Y m:ℝ→ℕ)
local notation "S'"=> R.family.path.levels.budget
local notation "e'"=> -(t+1/16:ℝ)/2
local notation "T"=> interval D s

structure CollectionR (r:ℝ)(N p:ℕ)(o:Fin n→Site (R.family.side (wheel R.family r) p))(u:(j:Fin n)→ R.family.label (d j))(q v:ℝ)(k m:ℕ)(x:R.family.label t):Prop where
   measure : quota R.family t m N p x ≤ q
   load : Cards.PaidAt R.family.S N p k (R.family.beta N p) v ((fun Z : Config G (R.family.side N p)=> ∏ j:Fin n,R.family.O N p (u j) (attachV R (wheel R.family r) (p:=p) o N j) Z) - R.family.O N p x 0)
include R Z W fx J
-- adapted Evidence from OPE.Prices.Circuit.funding -- keep Joined
-- costs along union exactly enough for arbitrary captions along geometry
-- no p-cost divergence; m+1=j allowed but no use here.
set_option maxHeartbeats 600000 in
lemma allocates (h:Lookup R m)(hp: Height R.family.S home OPE.run Y (1/2)) : ∃ q v : ℝ→ℝ, RateIs home OPE.run q (-(t:ℝ)) ∧ RateLE home OPE.run v (-(t+1/16:ℝ)/2)∧
   ∀ᶠ r in home,∀ N p:ℕ,∀ hj: wheel R.family r < N,∀ hk:Y r ≤ N,∀ o:Fin n→ Site (R.family.side (wheel R.family r) p), (∀ i,loops R.family (wheel R.family r) p (o i) (m r+1)=0) → Spaced (R.family.path.levels.budget (wheel R.family r)).B o →
      ∀ u:(j:Fin n)→ R.family.label (d j),(∀ j:Fin n,Spindle.paid R.family (d j) (wheel R.family r) N p (u j) ≤ H (Q r)^l)→
        let V:= Cells.center R.family.S p hk 0; (∀ i, Cells.Interior (V.chamber 0) (R.family.O N p (u i) ((R.family.S.toDepth hj.le p).embed (o i))))→ (∀ z:R.family.label t, Cells.Interior (V.chamber 0) (R.family.O N p z 0)) →
         ∃ x:R.family.label t, CollectionR R d t r N p o u (q r) (v r) (Y r) (m r) x:=by
   obtain ⟨W',r',D',E'⟩:= W.purchase; have hh:(1/2:ℝ)<1:=by norm_num
   let A:= E'.tabs; let P:= Stock.Tabs.chosen R.family.path.levels 1 A ∘ Y; have hP:Height R.family.S home OPE.run P (1/2):= hp.stock A
   have ha(r): Stock.Tabs.opens R.family.path.levels 1 (Y r) (P r):= Stock.Tabs.opened ..
   let M:= Fintype.card (Fin n); have hm:0<M:= Fintype.card_pos_iff.mpr ⟨J⟩
   let E:= E' -- may need .toPackage
   obtain ⟨y,hy,hF,hL⟩:= OPE.halls Z.simple E.halos M hm
   obtain ⟨χ,hχ⟩:= E.productCuts.mother
   let b(r:ℝ)(x:Fin n):=fly R.family.path.levels (d x) (Q r)/ (H (Q r))^l
   let z(i):= ManyCopies.initial R.family.path δ η (m i) (Q i) (y (Q i)) (∏ j,b i j) M
   have hG:= goingWheel R Z fx; have hv:RateIs home OPE.run (fun i=>∏ j,b i j) 0:=by
       apply (RateIs.prod (S:=Finset.univ) (fun i _=> (flyRate Z.simple hG (d i)).div ((runMount R Z fx).power l)) ageLarge).swap; simp
   have hZ:RateIs home OPE.run z 0:= (Height.gathered h.spine hG ageLarge (height0 hy hG) hv Z.simple M).swap (by ring)
   let e(i):= terminalCost C t (m i) (z i); let q i:=2*e i; let w i:= Real.exp (- (e')* OPE.run i); have hw:= RateIs.exp (-(e')) ageLarge; have hg:= key_cost h.spine ageLarge hZ Z.simple t; have hPaid:= terminalAfford Z.simple E hP h.spine ageLarge hh hZ t hg hw (by linarith only)
   let v i:=2*(stakes C (Y i) (P i)/ w i)
   refine ⟨q,v,((RateIs.const ageLarge zero_lt_two).mul hg).swap (by ring),?_,?_⟩
   · simp_rw [v,div_eq_mul_inv]; apply ((RateLE.const (2:ℝ) ageLarge).mul ((stock_price A Z.simple hp ageLarge).mul (hw.inv.pays ageLarge))).mono; try ring_nf; try simp only [le_refl]
   have hB:=briar C Z.simple E.accounting; have ht:= h.spine.step (ι|>.fits.mesh); let K i:=m i+1; have h_U:= (((height0 hB ht).power 2).add (RateIs.const ageLarge one_pos) ageLarge).mul ht.mesh
   filter_upwards [hp.mesh.overtakes (h_U.pays ageLarge) ageLarge (by norm_num),height_room hp h.spine ageLarge hh (lensScope C t), hP.earlier hh ageLarge h.spine,hp.grows.eventually_ge_atTop (R.family.ref t), hPaid,hZ.pos,h.log,eventually_all.mpr (fun j=> hG.grows.eventually_ge_atTop (R.family.ref (d j)))] with r hC hB hΦ hY hp hz hT he N p hj hk o hE hs u hc V hf ht
   let F(j):=R.family.O N p (u j) ((R.family.S.toDepth hj.le p).embed (o j)); let W(j):=b r j
   have hY':(R.family.path.levels.budget (K r)).B^2+1 ≤ (R.family.S.toDepth (((ha r).1.trans hΦ.le).trans (Nat.le_succ _)) p).count.val:=by
       let U:= R.family.S.toDepth (((ha r).1.trans hΦ.le).trans (m r|>.le_succ)) p
       have hR:((S' (K r)).B:ℝ)^2+1 ≤ U.count.val:= le_of_mul_le_mul_right (hC.le.trans_eq ((R.family.S.embeds_scale U).symm.trans (mul_comm ..))) (R.family.S.a_pos (K r))
       exact_mod_cast hR
   have hD:0 < (H (Q r))^l:= pow_pos (zero_lt_one.trans ((ι).fits.delayed _)) _
   have hw:(∀ i,0<W i):=fun i=>div_pos (inv_pos.mpr (pow_pos (zero_lt_one.trans ((ι).fits.delayed _)) _)) hD
   have hd(i): W i * Spindle.paid R.family (d i) (Q r) N p (u i) ≤ fly (ι) (d i) (Q r):=(mul_le_mul_of_nonneg_left (hc i) (hw i).le).trans_eq (div_mul_cancel₀ _ hD.ne')
   obtain ⟨x,hA,hK,hX⟩:= ManyCopies.joins R.family N (m r) p t (Y r) (P r) J (w r) W o (ha r).1 hΦ.le hj hT.2.le d u R.makes E.system E.literal (hχ t) A (ha r) (hY.trans (ha r).1) he hd hw hB hE hY' hs (hy.pos (Q r)) (hF (Q r)) (fun i _ hj=> hL (Q r) i hj.le) F (fun _=>rfl) hf ht hz le_rfl (Real.exp_pos _) hp.1 le_rfl hp.2
   have he (Z₀: Config G (R.family.side N p)) : (∏ j:Fin n,R.family.O N p (u j) (attachV R (wheel R.family r) o N j) Z₀)= ∏ i,F i Z₀ := Finset.prod_congr rfl fun j _=>by dsimp only [attachV,F]; rw [vect C _ p N (o j) hj.le]
   exact ⟨x,hA,(funext he).symm ▸ (show Cards.PaidAt R.family.S N p (Y r) (R.family.beta N p) (v r) ((fun U=> ∏ i,F i U)-R.family.O N p x 0) from ⟨hk,hK,hX⟩)⟩ -- ▸ whole expression uncertain
-- deploy combining PAGED exact labels from ticket. no exterior here.
variable {x:Points n}(b:ℝ→ Fin n → Cover)
lemma assures (ho:Stands L D s) (h:Lookup R m)(hp: Height R.family.S home OPE.run Y (1/2)) : ∃ q v:ℝ→ℝ, RateIs home OPE.run q (-(t:ℝ)) ∧ RateLE home OPE.run v (-(t+1/16:ℝ)/2)∧
   ∀ (x:Points n)(b:ℝ→ Fin n → Cover), x∈generic n → Tendsto (fun r=>tag (role R.family r) (b r)) (interval D s) (𝓝 x) →
    ∀ᶠ r in T,∀ᶠ p:ℕ×ℕ in L.lens,∀ w:(i:Fin n)→ R.family.label (d i), (∀ i:Fin n,Paid L r w i ≤ (R.family.path.levels.clock.hatBeta (wheel R.family r))^l)→
     let o:= wrap (R.family.side (wheel R.family r) p.2) ∘ b r; let u(i):= atRef L (d i) r p (w i);
     ∃ z:R.family.label t,CollectionR R d t r p.1 p.2 o u (q r) (v r) (Y r) (m r) z:=by
   obtain ⟨l',hl⟩:= (eventually_all.mpr (fun j:Fin n=> eventually_ge_atTop (1+8*(d j+1)+l))).exists
   obtain ⟨q,v,hq,hv,hQ⟩:= allocates R Z fx W J d l' t Y m h hp
   refine ⟨q,v,hq,hv,fun x b he hT=>?_⟩
   have ht:T ≤ home:= (homes D).comp s.cofinal; have hz:= mintages R Z fx Y m b h ht ((hp.earlier (by norm_num) ageLarge h.spine).mono fun _ h=>h.le) hT he
   have ha:∀ᶠ r in T, R.family.S.a (L.level r) ≤ r:=by
       change ∀ᶠ i:ℕ in atTop, R.family.S.a (L.level (offsetPath D s i)) ≤ offsetPath D s i
       filter_upwards [s.cofinal.eventually D.proper] with i hi
       rw [ho.match_length]; exact hi.1
   filter_upwards [hz,hQ.filter_mono ht,(turnsWheel C|>.mono_left ht).eventually_ge_atTop 1,eventually_all.mpr (fun i=> (goingWheel R Z fx).grows.eventually_ge_atTop (R.family.ref (d i))|>.filter_mono ht),eventually_all.mpr (fun i=>Z.reach.growing.eventually_ge_atTop (R.family.ref (d i))|>.filter_mono ht),ha,(reverseSpoke C fx Z.simple).filter_mono ht] with r hr hp he hU hm ha hA
   let k:=Q r; let g:=Y r
   have hY:= (OPE.Cards.largeMesh f).mono_left L.certified
   filter_upwards [(large_mesh f (g)).filter_mono L.certified,(large_mesh f (k+1)).filter_mono L.certified,(large_mesh f (L.level r)).filter_mono L.certified, (late_period hr.marsh).filter_mono L.certified,hY.eventually (near_center C g t R.makes), eventually_all.mpr (fun i=> hY.eventually (near_center C g (d i) R.makes))] with p hg hk hM hN hT hS w hx o u
   have h':k<p.1:=hk; have hR :1 ≤ R.family.path.levels.clock.hatBeta k:= ((ι).fits.delayed k).le
   have hw (i):Spindle.paid R.family (d i) k p.1 p.2 (u i) ≤ R.family.path.levels.clock.hatBeta k^l':=by
       have hv: a (L.level r) / a k ≤ R.family.path.levels.clock.hatBeta k^8 := (div_le_iff₀ (R.family.S.a_pos _)).mpr ((ha.trans hA).trans_eq (mul_comm ..))
       have hs:= YM.RG17.ReadoutCompat.monies (p:=p.2) R fx L W (d i) 8 l k (L.level r) (w i) (r:=r) rfl he (hm i) (hU i) h'.le hM hv (hx i)
       exact ((le_mul_of_one_le_left (paid_pos ..) (col_ge C k)).trans (show moneys C (d i) k p.1 p.2 (u i) ≤ _ from hs)).trans (pow_le_pow_right₀ hR (hl i))
   have hF:Edition.Spaced (R.family.path.levels.budget k).B o∧ ∀ i,loops C k p.2 (o i) (m r+1)=0∧ R.family.S.place (o i)= R.family.S.gridPoint k (b r i) := hN
   exact hp p.1 p.2 h' hg o (fun i=>(hF.2 i).1) hF.1 u hw (fun i => hS i hg _ _ (by rw [R.family.S.embeds_place, (hF.2 i).2]; exact (hr.fit i).le.trans (R.family.S.strictAnti.antitone (hr.first.trans (Nat.le_succ _)))) _) (fun i=> hT hg p.2 _ (by rw [latzero]; simp [(R.family.S.a_pos _).le]) _)
end YM.RG17

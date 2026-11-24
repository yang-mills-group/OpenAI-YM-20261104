import YM.RG05Readout.Capture.Invoices
/-!
# Pencilization from grouped Blade

Price includes an acquired remounted size charge x from Salt. Carry to
true weighted representative using all Root children. Include `Travel`
with test bills, not a route replacing all densities on that Canvas.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge} {C:Family G} {N m p d:ℕ}
local notation "Z"=> C.path
local notation "R₀"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "F"=> C.labels.level
local notation "S"=> C.localSection
local notation "Y"=> C.params
local notation "Ω"=> C.path.levels.clock.op m p
local notation "L"=> C.path.S.block m
local notation "κ"=> kappa C.path
local notation "v"=> ((L).val:ℂ)^d
variable {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}{s X a x u v₀ A c α β :ℝ} {W:PulseC}{o:Site (C.side (m+1) p)} {P: Three G (C.side (m+1) p)}{Q:Three G (C.side m p)}
lemma Travel.growth (hw:Priced d W u)(hq:Ride Ω o 0 D v P Q x):Travel C N m p d o D (glyph W P) (glyph W Q) (u*x):=by
    intro φ t hc; simp only [glyph_apply]
    have hx:= hq.matchPay (W φ) (W φ) v (mul_comm ..); apply hx.cost; rw [max_self,mul_right_comm]; exact mul_le_mul_of_nonneg_right (hw φ t hc) hq.nonneg
-- Coarse fees
open Finset
local notation "Ct"=> (Fintype.card (Letter d):ℝ)
local notation "Amt"=> A*a
variable (h:C.Makes)(hm:m<N) (hz:Plated (C.labels.level d) C.path (C.localSection d) C.params m N p D A) (hA:1 ≤ A)
set_option quotPrecheck false
local notation "CapF"=> Ct*X^2
noncomputable def publicCost (d:ℕ)(X:ℝ):= 16*(1+(Fintype.card (Letter d):ℝ))*X^4
section
variable (he:Cursor C N m p d s X)(hg:SoundDoor (C.path.levels.clock.op m p) D)
include he hz h hm hg hA
local notation "Tim"=> publicCost d X * Amt
lemma decompose (hW: Priced d W 1)(ho:(Ω).ratio.parent o=0)(hp: Useful M P)(hB:MergeProof.Float.Blade (M) o P.snd.1 (profile ((M).activities) P.snd.2) 0 a)(ha:0≤a) :
    ∃ (Q':Tape G (C.side m p)),∃ y g, Course (D:=D) (d:=d) o (glyph W P) Q' y g Tim Tim ∧ size y ≤ Tim:=by
    have h1 := he.fits; have h0:= zero_lt_one.trans_le h1; have hA' := zero_lt_one.trans_le hA; let T:= Amt; have ht: 0≤ T:=mul_nonneg hA'.le ha
    obtain ⟨K,hK,hT,hP,hQ⟩:= peppers h hz ho hm hg hA'.le hp hB ha; let c:= (F d).coeffSize K.x
    have hV: (A+2)*a+ X*c ≤ (3+ X)*T:=by change c ≤ T at hP; rw [add_mul (3:ℝ)]; apply add_le_add _ (mul_le_mul_of_nonneg_left hP h0.le); unfold T; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by linarith only [hA]) ha
    have hV' : X*c ≤ X*T:= mul_le_mul_of_nonneg_left hP h0.le; have hi: (X*c+(0+X*c)+Amt) ≤ 3*X*T:=by have hr:T ≤ X*T:=le_mul_of_one_le_left ht h1; change _+_+ T ≤_; linarith only [hr,hV']
    let Wℓ(i:Letter d):= W (line i);
    have hr(i:Letter d): ∃ (Q:Tape G (C.side m p)),∃ y g, Course (D:=D) (d:=d) o (Wℓ i • glyph (readJ i 0) P) Q y g (X*(3*X*T)) (X*(X*((3+X)*T)))∧ size y ≤ X*(X*T):=by
       obtain ⟨Q,hB',hC,hR,hG,hI⟩:= Cursor.reshape (D:=D) h hm he K (h:=kept i) (Nat.sub_le ..) le_rfl hg hK hT hQ
       let f:=glyph (readJ i 0) (invoice Q 0 (S (kept i)) R₀); have hp':‖W (line i)‖ ≤ X := (hW _ _ (he.card i)).trans_eq (one_mul _)
       have hF : Travel C N m p d o D (glyph (readJ i 0) P) f (X*((3+X)*T)):= Travel.growth (fun v₁ z hV=> (fees d i box0 hV).trans (mul_le_mul_of_nonneg_right he.earns hV.nonneg)) (hR.cost hV)
       let z:=chunk i Q.x; let E:= W (line i); have hv:= printed_one i Q hB' (rem_mono hC hi)
       refine ⟨E • f,E • z,E • chunk i (Trace.Physical.Germ.projection _ C.params (R₀).p.threshold 0 Q), ?_,?_⟩
       · refine ⟨((hv.twist (he.sense d le_rfl).order (he.sense d le_rfl).power E).grow (mul_le_mul_of_nonneg_right hp' (by positivity))), ((hF.smul E).extend (mul_le_mul_of_nonneg_right hp' (by positivity)))⟩
       rw [size_smul,size_chunk i]; exact mul_le_mul hp' (le_trans hG hV') (Work.G08.size_nonneg ..) h0.le
    choose U f g hE hW' using hr
    have hv(i:Letter d): Wℓ i = W (line i):=rfl
    obtain ⟨Q,hJ,hC,hR,hG,H⟩:= Cursor.reshape (D:=D) h hm he K (h:=0) (Nat.zero_le _) le_rfl hg hK hT hQ
    let V:= glyph (recollect d W) (invoice Q 0 (S 0) R₀); have hπ :=recall_price d hW;
    have hz : Course (D:=D) (d:=d) o (glyph (recollect d W) P) V 0 0 (4*X*T) ((3+X)*T):=by
       have h:= printed_high (C:=C) (o:=0) (recollect d W) (tail_rec d W) hπ Q hJ (rem_mono hC hi)
       refine ⟨h.grow ?_,(Travel.growth hπ (hR.cost hV)).extend (le_of_eq (one_mul _))⟩
       linarith only [le_trans hG hV'] -- risk normalizer
    rw [show glyph W P=(∑ i:Letter d,Wℓ i • glyph (readJ i 0) P)+glyph (recollect d W) P from ?_]; swap
    · ext1 v₁; change W v₁ • P=_; rw [expands d W v₁, add_smul,Finset.sum_smul]; simp only [LinearMap.sum_apply,LinearMap.smul_apply, LinearMap.add_apply,glyph_apply, mul_smul,hv]
    let E:=3*X*T; have hF':= Course.faith he h hm hg Finset.univ (fun i _=> hE i); simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hF'
    have hπ': (1+Ct)*X^4 ≥ X^4:=le_mul_of_one_le_left (by positivity) (by linarith only [Nat.cast_nonneg (α:=ℝ) (Fintype.card (Letter d))]); have hX: X^2 ≤ X^4:=pow_le_pow_right₀ h1 (by norm_num); have hX': X ≤ X^2:= (pow_one _).symm.trans_le (pow_le_pow_right₀ h1 (by norm_num)); have hvC:X^3≤ X^4:=pow_le_pow_right₀ h1 (by norm_num)
    let Y' := publicCost d X; have htC:0 ≤ Ct:=Nat.cast_nonneg _; have hs:Ct*X^4 ≤ (1+Ct)*X^4:=mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)
    -- prove simple
    have he' : Ct*X^2 ≤ (1+Ct)*X^4:= (mul_le_mul_of_nonneg_left hX htC).trans hs
    let T':=∑ i,U i
    refine ⟨T'+V,(∑ i,f i)+0,(∑ i,g i)+0,⟨?_,?_⟩,?_⟩
    · have heq:= hF'.paid.addP hz.paid (h.wilson.represents N p m hm.le).good (he.sense d le_rfl).order (he.sense d le_rfl).power
      apply heq.grow; apply le_trans (b:=(Ct*X^2*3+4*X)*T) (le_of_eq (by ring)) (mul_le_mul_of_nonneg_right _ ht); unfold publicCost; linarith only [he',hX',hX,hπ',zero_le_one.trans (one_le_pow₀ (n:=4) h1)] -- zero...
    · apply (hF'.ready.add hz.ready h hm hg).extend; apply le_trans (b:=(Ct*X^2*3+Ct*X^3+(3+X))*T) (le_of_eq (by ring)) (mul_le_mul_of_nonneg_right _ ht); unfold publicCost; linarith only [he',(mul_le_mul_of_nonneg_left hvC htC).trans hs,hX,hX',h1,hπ']
    rw [add_zero]; apply (size_sum ..).trans ((sum_le_sum (fun i _=> hW' i)).trans _); rw [Finset.sum_const, card_univ, nsmul_eq_mul]; change Ct*(X* (X*T)) ≤ Y'*T; apply le_trans (b:=Ct*X^2*T) (le_of_eq (by ring)); apply mul_le_mul_of_nonneg_right _ ht; unfold Y' publicCost; linarith only [he',hπ',pow_nonneg h0.le 4]
end
-- use SignedPrice. X≤LD. supports and spin not implicit
variable {B B':ℝ}
local notation "Ld"=> Copper.ld C.path.levels m
include h hA hm hz
set_option maxHeartbeats 500000 in
lemma cooled (hw: Copper.SignedPrice C m p d N D B B')(hW:Priced d W 1)(ho:(Ω).ratio.parent o=0)(hp: Useful M P)(hB:MergeProof.Float.Blade M o P.snd.1 (profile (M).activities P.snd.2) 0 a)(ha:0≤a) :
    let T:= publicCost d Ld *Amt
    ∃ (Q':Tape G (C.side m p)),∃ y g, Course (D:=D) (d:=d) o (glyph W P) Q' y g T T ∧ size y≤ T:=by
    intro T; obtain ⟨s,K,c,b,T',V,hP,hTurns,hQ,hR,hJ,hS⟩:=hw.author
    obtain ⟨Q',y,g,hE,hY⟩:= decompose h hm hz hA hP.cursor hP.door hW ho hp hB ha
    have hc:= hP.cursor.fits; have hc':=zero_le_one.trans hc; have hgK:=zero_le_one.trans hP.posp; have hα:= hP.a_pos; have hv : 0≤ aCost d K:= aCpos hc'; have hs' :=hP.b_pos
    have h' : K ≤ Ld:=by
       have he:K≤tollP d K c b:=by
           have hV:K≤aCost d K:=le_add_of_nonneg_right (by positivity)
           unfold tollP; exact hV.trans (le_mul_of_one_le_right hv (by nlinarith only [hgK,hs',mul_nonneg hc' hgK]))
       have hp':0 ≤ tollV d L K c (Doors.rate L) b:=by unfold tollV; positivity -- check
       linarith only [he,hJ,mul_nonneg (mul_nonneg hp' (zero_le_one.trans (shift_pays (R:=M)))) (zero_le_one.trans hw.pos.1),hc] -- args
    have he : publicCost d K*Amt ≤ T:=by unfold T publicCost; gcongr
    exact ⟨Q',y,g,hE.rise he he,hY.trans he⟩
end YM.RG05Readout.Address

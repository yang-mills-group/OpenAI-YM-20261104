import YM.RG05Readout.Shadows.Offer
/-!
# Coherence of alternative tapes

Combine steps AFTER centered per-child solver. Coarse residual receipt agrees
in *jet*, by projection surival. Actual signed branch extends with the priced
counter path using that identity and carry on this auction. No selecting along
period.Jet, no matching arbitrary representations from theorem on values.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Shadow
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View Address
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {N m n b p d:ℕ}{D:Address.Rail C}{B:ℕ→ℕ→ℝ}{x e E e':ℝ}
set_option quotPrecheck false
variable (h:C.Makes){V:Sight C d p}{S:Emblems C d}
local notation "Z!"=> C.path.levels
local notation "R₀"=> C.path.rep N p
local notation "Ω"=> C.path.levels.clock.op
local notation "ζ"=> C.S.block
local notation "F₀" => Palette C d
local notation "W₀"=> fun i =>C.side i p
local notation "κ₁"=> kappa C.path
local notation "ℓ"=> Copper.ld C.path.levels
local notation "ν"=> C.path.levels.clock.J
local notation "O"=> Address.Bud C p m
local notation "λ"=> C.path.S.block m
local notation "χ"=> ((C.path.S.block m).val:ℂ)^d
local notation "q"=> trim (C.path.S.block m)
local notation "X'"=> (R₀ (m+1))
local notation "X"=> R₀ m
local notation "Y!"=> Address.child C p m
section
lemma topCell_average {V:Type*}[Fintype V]{n:Side}{f:V→Tape G n}: pulseOut (Address.average f)= Address.average (fun i=> pulseOut (f i)):=by
   unfold Address.average; funext i; unfold pulseOut; rw [LinearMap.smul_apply,LinearMap.sum_apply]; change (Fintype.card V:ℂ)⁻¹ • (∑ j, f j i).fst= (Fintype.card V:ℂ)⁻¹ • (∑ j,fun i=>(f j i).1) i; rw [Finset.sum_apply,Prod.fst_sum]
end
variable (hw:Awake D B b d) (hv: Spine D B h b p d N V S)
section
variable (H: ∀ i:ℕ,Tape G (C.side i p))(Y:ℕ→ Palette C d) (ht:Halo D (eC:=h) b b n p N d V Y H e)
local notation "W"=> tab C E n
local notation "K₁"=> advances S Y b
local notation "Π"=> Ω m p
local notation "Σ!"=> (R₀ (m+1))
local notation "TR"=> (fun i:O=> Many.headFee C p m i)
include hv hw h ht
set_option maxHeartbeats 800000 in
lemma shadows {F:Address.Bud C p m→Tape G (C.side (m+1) p)} (hb:b ≤ m)(hn:m<n)(hN:n ≤ N)
    (hF:∀ i,∃ z, Printed C d (R₀ (m+1)) 0 (κ₁ (m+1)) (F i) z 0 (tab C E n (m+1)))(hQ:∀ i:Address.Bud C p m,pulseOut (F i)=pulseOut (H (m+1))) :
    let D0:= D N p m (hn.trans_le hN); let u:= keys0 (p:=p) (C:=C) h (hn.trans_le hN)
    ∃ T: Address.Bud C p m→Tape G (C.side m p), let V':= Address.average T - V m (Y m); (∀ i,Travel C N m p d (Y! i) D0 ((orient u (F i) i).comp (TR i)) (T i) (ℓ m* W (m+1))) ∧ (∃ z,Printed C d (R₀ m) 0 (κ₁ m) V' z 0 (W m))∧ pulseOut V'=pulseOut (H m):=by
    choose U hP using hF; have hk:= hn.trans_le hN
    have hs:= hw.toll p m N hb hk
    intro z u; let g:= V m; have hX:= hv.legal m hb hk.le
    obtain ⟨T,w,hR,hY₁,v',hV⟩:= dark_skew (D:=z) h hk u hs F U hP g hX
    rw [← tab_step (m:=m)] at hV hY₁
    let A:= Address.average T; let f:=A-g w; have hA: pulseOut A=pulseOut (H m+g (Y m)):=by
       rw [funext (fun x=> proceeds C p m N d (H (m+1)) (H m+g (Y m)) x (ht.gate m hb hn hk))]
       funext x; obtain ⟨Q,hq,hx⟩:=Native.Cap.cost x (d+2)
       have hu(i:Address.Bud C p m): (pulseOut (T i)) x= blast C.path N p m d ((pulseOut (H (m+1)) ((TR i) x)) ∘ Lattice.pull 1 (Y! i)) :=by
          have ht:= (hR i x Q hx).exactStep; refine ht.trans ?_; rw [← hQ i]; rfl
       unfold A; rw [topCell_average]; unfold Address.journey Address.average; rw [Pi.smul_apply,Finset.sum_apply]; simp_rw [hu]
    -- Has charges on both sides of hA even though different lanes
    have hr:= h.wilson.represents N p m hk.le; obtain ⟨s,K,c,β,T'',Q,hS,hT⟩:=hs.author; let hp:= hS.cursor.sense d le_rfl
    obtain ⟨q₀,hq₀⟩:= hX.capacity0 w; obtain ⟨u',hU⟩:= hX.capacity0 (Y m); obtain ⟨Y',hY⟩:= ht.empty m hb hn.le
    have hY':= germ_eyelet hw (P:=H m+V m (Y m)) (F:=A) (hr:=hY.addP hU hr.good hp.order hp.power) (u:=v'+q₀) (z:=0+w) (x:=W m+B d m*size w) (by have he:=hV.addP hq₀ hr.good hp.order hp.power; simpa only[g,sub_add_cancel] using! he -- `zero_add`
      ) hb hk hA
    have heW:w=Y m:=by simpa only[zero_add] using hY'
    refine ⟨T,?_⟩; rw [heW] at hV
    intro V'; refine ⟨hR,⟨v',hV⟩, ?_⟩
    change pulseOut (A-g (Y m))=_; rw [show pulseOut (A-g (Y m))=pulseOut A - pulseOut (g (Y m)) from rfl,hA]; exact add_sub_cancel_right ..

-- use skew `Travel` to actual ticket along discrepancy lane
lemma Spirits (hk:12 ≤ ν b) (hb:b ≤ m)(hn:m < n)(hN:n ≤ N)(he:E ≥ e)(hc:0 ≤ E)
    {T:Address.Bud C p m→ Tape G (C.side (m+1) p)}(hF:∀ i,∃ z, Printed C d (R₀ (m+1)) 0 (κ₁ (m+1)) (T i) z 0 (tab C E n (m+1))) (hQ:∀ i,pulseOut (T i)=pulseOut (H (m+1))) :
    let D0:= D N p m (hn.trans_le hN); let u:= keys0 (p:=p) (C:=C) h (hn.trans_le hN)
    ∃ (P:Tape G (C.side m p)), (∃ z, Printed C d (R₀ m) 0 (κ₁ m) P z 0 (tab C E n m))∧ pulseOut P=pulseOut (H m) ∧ ∃ (T':Address.Bud C p m→ Tape G (C.side m p)), Address.average T'=P+V m (K₁ m)∧ ∀ i,Travel C N m p d (Y! i) D0 ((orient u (T i+ V (m+1) (K₁ (m+1))) i).comp (TR i)) (T' i) (32*(ℓ m)^2* W (m+1)):=by
    intro D0 u
    obtain ⟨Y₀,hf,hP,hA⟩:= shadows h hw hv H Y ht hb hn hN hF hQ
    have hi(i:ℕ) : tab C e n i ≤ W i:= mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
    have hO(i:ℕ)(hb:b ≤ i)(hi':i ≤ n): size (K₁ i) ≤ 20*W i:= overture h hv hk hN hc (fun i h h' => (ht.spends _ h h').trans (hi i)) hb hi'
    let P:=Address.average Y₀-V m (Y m); let Y':=K₁ (m+1)
    have hz: S m Y'= K₁ m -Y m:= adv_leans hb; have hf':= hv.follows m hb (hn.trans_le hN); obtain ⟨F,hx,hX⟩:= hf'.goes Y'; refine ⟨P,hP,hA,Y₀+F,?_,fun i=>?_⟩
    · rw [ave_add,← hX,hz,map_sub]; unfold P; abel
    rw [orient,LinearMap.comp_add,LinearMap.add_comp]; let Q:= hw.toll p m N hb (hn.trans_le hN); obtain ⟨s,K,c,β,x',Q',hS,-⟩:=Q.author
    apply ((hf i).add (hx i) h (hn.trans_le hN) hS.door).extend
    have hp:= hf'.strength Y'; let t:=amplify d C (ζ m) Y'; have hs:=lamp_nn (C:=C) m; have hL:0 ≤ ℓ m:= zero_le_one.trans hs
    have ht' := tab_pos (n:=n) (C:=C) (i:=m+1) hc; have hV : W m≤ W (m+1):=by rw [tab_step (m:=m)]; exact mul_le_of_le_one_left ht' (light _)
    have hV':size (S m Y') ≤ 21* W (m+1):=by rw [hz,sub_eq_add_neg]; apply (size_add ..).trans; rw [size_neg]; linarith only[hO m hb hn.le,(ht.spends m hb hn).trans (hi m),hV]
    have hw : size t≤ ℓ m* (21*W (m+1)):= hp.1.trans (mul_le_mul_of_nonneg_left hV' hL)
    have he' : ℓ m≤(ℓ m)^2:= (pow_one _).symm.trans_le (pow_le_pow_right₀ hs (by norm_num))
    linarith only [mul_le_mul_of_nonneg_left hw hL,mul_le_mul_of_nonneg_right he' ht',mul_nonneg (pow_nonneg hL 2) ht'] -- unfold t
end
end YM.RG05Readout.Shadow

import YM.SignedWilsonExpansion.Purchase.Schedule
/-! Backward/forward absolute scale-window picks before dates. Use fallback padding only before
realization. Horizon through finitely many nested steps, require common prices.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases.Schedules
open Asymptotics Wilson Gauge RG Push Lattice Source PriceCompiler UVClock WilsonCoeffUV.Bank PathCost
open Set Filter Function Real Next.Rank Perch Commission
open RG.Supply
open scoped Topology Classical BigOperators
variable {G:Gauge} {M:Levels G}{ι κ:Type*}{A K S Q B ρ:ι→ℝ}{N j k p i m:ℕ}{L:Filter ι}
lemma dataG (S:Schedule)(x:ℝ): ∃ i,x≤ S.scale i:= (S.divergent.eventually_ge_atTop x).exists
abbrev berthX (S:Schedule)(x:ℝ): ℕ:= Nat.find (dataG S x)
lemma berth_yes (x): x≤ M.S.scale (berthX M.S x):= Nat.find_spec (dataG _ _)
lemma berth_no {x}(v:i<berthX M.S x): M.S.scale i<x:= lt_of_not_ge (Nat.find_min (dataG ..) v)
variable (h:Rise B L)(b:GentleS M)(g:G.Simple)
-- crossing supplies floors & epoch EXACT asymptotic relative (payment condition uses ≈);
-- alternative Room.J j<M.K unaligned ceil chosen.At most Y/ρ slack, actually o(Y).
include h b g in
lemma door (x:ι→ℝ)(p:IsEquivalent L (fun i=> G.slopeConstant*x i) B):
    Epoch L B M (fun i=> berthX M.S (x i)) ∧ (fun i=> M.S.scale (berthX M.S (x i))- x i)=o[L] (Spread B):=by
    let W(i):= berthX M.S (x i); let w(i):= W i -1; have ht:= p.isBigO.exists_pos
    have hg:= Gauge.slopeConstant_pos g; have hx:Rise x L:= tendsto_atTop.mpr fun a=> (( tends h p ).eventually_ge_atTop ( G.slopeConstant * a )).mono fun i hi=> by nlinarith only [hg,hi]
    have hh:Rise (M.S.scale ∘ W) L:= tendsto_atTop_mono (fun i=>berth_yes _) hx; have hv: Tendsto W L atTop:=tendsto_atTop.mpr (fun i=> (hh.eventually_gt_atTop ( M.S.scale i )).mono fun k h'=> by_contra fun hx=> not_le.mpr h' (scales M.S (by omega : W k≤ i)))
    have hL(i):1≤((M.S.block (w i)).val:ℝ):=by exact_mod_cast Nat.succ_le_of_lt (M.S.block _).property
    let T(i):= M.clock.bar+G.slopeConstant*x i; have ht: IsEquivalent L T B:= p.const_add_of_norm_tendsto_atTop (c:=M.clock.bar) (show Tendsto (norm ∘ B) L atTop from h.congr' ((h.eventually_gt_atTop 0).mono fun i hi=> Eq.symm (Real.norm_of_nonneg hi.le)))
    have pW:=hv.eventually_gt_atTop 0; let k(i):= log ((M.S.block ( w i ) ).val:ℝ); let ℓ(i):=M.clock.hatBeta ( w i ); let S:=Spread T
    have ht':Rise T L:= tends h ht
    have he:Tendsto (log∘ ℓ) L atTop:= Real.tendsto_log_atTop.comp ((hat_rateM M g).comp (tendsto_atTop.mpr (fun i=> (hv.eventually_gt_atTop i).mono fun a ha=> by unfold w; omega)))
    have h_o : k=o[L] (Spread B) :=by
        have hy:(log ∘ S)=o[L] (Spread B):= ((show (log)=o[atTop] (fun i=>i) from by simpa using! (isLittleO_log_rpow_atTop zero_lt_one)).comp_tendsto (y_rise ht')).trans_isBigO ( spread_tie h ht ).isBigO; apply IsBigO.trans_isLittleO _ hy; apply IsBigO.of_bound'; filter_upwards [pW] with i hi; rw [Real.norm_of_nonneg (Real.log_nonneg (hL i))]; let v:= w i; have hv :v<W i:= by unfold v w; omega
        have hp:= M.fits.delayed v; have hh: ℓ i≤ T i:= add_le_add_right (mul_le_mul_of_nonneg_left (berth_no hv).le hg.le) _; have ht:1≤ℓ i:= hp.le
        have h': ((M.S.block v).val:ℝ)≤ log (log (ℓ i)):= b _; refine le_trans (b:=log ( S i )) (Real.log_le_log ( zero_lt_one.trans_le ( hL i ) ) ?_) (le_abs_self _); exact le_trans h' ((log_le_self (log_nonneg ht)).trans (log_le_log ( zero_lt_one.trans_le ht ) hh))
    have hy : (fun i=>M.S.scale ( W i )-x i)=o[L] (Spread B):=by
        apply IsBigO.trans_isLittleO _ h_o; apply IsBigO.of_bound'; filter_upwards [pW] with i hi; have he: x i≤ M.S.scale ( W i ):= berth_yes _; rw [Real.norm_of_nonneg (sub_nonneg.mpr he)]; refine le_trans (b:=k i) ( ?_ ) (le_abs_self _); let t:= w i; have hz: W i=t+1:=by unfold t w; omega
        have hx:= berth_no (by omega: t<W i)|>.le; let hH:= M.S.scale_succ t; rw [← hz] at hH; unfold k; change _≤log ((M.S.block t).val:ℝ); change M.S.scale t≤ x i at hx; linarith
    refine ⟨IsLittleO.isEquivalent ?_,hy⟩; change ( ( M.clock.hatBeta∘ W ) - B ) =o[L] B; have hU:= (( hy.isBigO.trans_isLittleO ( polyLittle h ( A:=Spread B ) ⟨1,by simp; exact isBigO_refl _ _⟩ ) ).const_mul_left G.slopeConstant ); refine (ht.isLittleO.add hU).congr_left (fun i=>?_) ; change _ + _ = M.clock.hatBeta ( W i )-B i; simp only [ Pi.sub_apply,T,Calendar.hatBeta ]; ring
include h
variable {F:ι→ℝ} {k₁ k₂ k₃:ι→ℕ}
lemma noteUpper (v:∀ᶠ i in L,0≤K i)(ht:∀ᶠ i in L,K i≤F i)(hs:Wage L (Spread B) 1 F): Wage L (Spread B) 1 K:=by
     apply Wage.rel hs; refine IsBigO.of_bound' (?_); filter_upwards [ht,v] with i hi hv; rw [Real.norm_of_nonneg hv]; exact hi.trans (le_abs_self _)
-- interval costs for Arc.VT calendar.Width.Epoch numeric.Job AFTER stakes assumptions.
abbrev widthArc (M:Levels G) (k l:ℕ):= 1+(M.S.scale l-M.S.scale k)
abbrev hemisphere (M:Levels G) (L:Filter ι)(B:ι→ℝ)(k l:ι→ℕ): Prop:= Wage L (Spread B) (1:ι→ℝ) (fun i=> M.S.scale (l i)- M.S.scale (k i))
include g b in
lemma colorIncome (v:hemisphere M L B k₁ k₂)(p:∀ᶠ i in L,k₁ i≤k₂ i)(q:Epoch L B M k₁): ∃ f:ι→ℝ,Wage L (Spread B) 1 f ∧ ∀ᶠ i in L,1 ≤ f i ∧ widthArc M (k₁ i) (k₂ i)≤ f i ∧ ∀ j≤k₂ i, ((M.S.block j).val:ℝ)≤ f i :=by
    let t(i):= widthArc M (k₁ i) (k₂ i); let k(i):= ((M.S.block (k₂ i)).val:ℝ); let f(i):= t i + k i; refine ⟨f, Wage.plus (y_rise h|>.eventually_ge_atTop 1) ( Wage.plus ( y_rise h |>.eventually_ge_atTop 1 ) (Wage.unitC (1:ℝ)) v ) ( hull h M g b (epoch_equiv h q v) ),p.mono fun i hi=> ?_⟩
    have ht:1≤t i:= le_add_of_nonneg_right (sub_nonneg.mpr (scales M.S hi)); have hp: t i≤f i:= le_add_of_nonneg_right (Nat.cast_nonneg _); exact ⟨ht.trans hp,hp, fun j hj=> (stepGrowth M hj).trans (le_add_of_nonneg_left ( zero_le_one.trans ht ))⟩ -- ℕ width lemma remains
include b g in
lemma berthSketch (z:ι→ℝ)(e:Epoch L B M k₁)(s:Wage L (Spread B) 1 (fun i=> z i-M.S.scale (k₁ i))) : Epoch L B M (fun i=>berthX M.S (z i)) ∧ (fun i=> M.S.scale ( berthX M.S (z i)) - z i) =o[L] (Spread B):=by
     apply door h b g z; let H:= (polyLittle h s).const_mul_left G.slopeConstant; refine (IsLittleO.isEquivalent ( (( e.isLittleO.add H ).sub ( polyLittle h ( Wage.unitC M.clock.bar ))).congr_left (fun i=>?_) )); simp only[Pi.sub_apply,Function.comp_apply,Calendar.hatBeta]; ring
include b g in
lemma precursor (v:Epoch L B M k₁): Epoch L B M (fun i=> k₁ i -1):=by
     let x(i):= k₁ i -1; let hv:= fee_Θ h M g v; let hx:= (stairLimit h M g b v ( Eventually.of_forall (fun i=> (?_:x i≤k₁ i)))).isBigO; swap; · exact Nat.sub_le ..
     apply epoch_equiv h v; refine Wage.fix (Wage.neg ( Wage.ascend ( Wage.enroll hx ) ⟨1,(by simp; exact isBigO_refl _ _)⟩ )) ( (hv.eventually_gt_atTop 0).mono fun i hi=>?_ ) (.refl ..); dsimp only; rw [show x i+1=k₁ i from Nat.sub_add_cancel hi]; unfold x; abel
lemma predecessorMesh (v:Tendsto k₁ L atTop) : Tendsto (fun i=>k₁ i-1) L atTop:= tendsto_atTop.mpr fun i=> ( v.eventually_gt_atTop i ).mono fun _ t=> by omega
end YM.SignedWilsonExpansion.Purchases.Schedules

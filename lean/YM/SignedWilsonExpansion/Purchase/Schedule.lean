import YM.SignedWilsonExpansion.Purchase.Solier
import YM.Push.PRICE_COMPILER.Basic
/-! # Common task scheduling scales
We pay for length on post β (before choosing actual calendar). This gives all ranges through fixed cabinets including eventual cut.J & K.
- Dispersion.leasure: an actual step need not near integral r/ρ, we pay lattice alignment through arc estimates.
- Lantern.Y(width) price from ALL steps window.W, not `lengthS` cost at entry only.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases.Schedules
open Asymptotics Wilson Gauge RG Push Lattice Source
open PriceCompiler UVClock WilsonCoeffUV.Bank PathCost
open Set Filter Function Real Next.Rank Perch Commission
open RG.Supply
open scoped Topology Classical BigOperators
variable {G:Gauge} {M:Levels G}{ι κ:Type*}{A K S Q B ρ:ι→ℝ}{N j k p i m:ℕ} {f b:ℕ}{L:Filter ι}
-- prices for Length. log β. Ask post `exp exp L`, enough for η annulus.Run; geometry arc.Price.C.T includes upper for τ posts.
abbrev deepLength (s:Sheet G) (D:Rolls s) (j:ℕ): ℝ:= Real.exp (Real.exp ((D.L j).val:ℝ))
def GentleS (M:Levels G): Prop:=∀ i, ((M.S.block i).val:ℝ)≤ Real.log (Real.log ( M.clock.hatBeta i ))
lemma bought_length {s:Sheet G}{D:Rolls s}{Z: Protection D}{U:Delays Z}{Y:Bar U}{I:Wait Y}
    (h:Paid I M)(p: deepLength s D ≤ U.betaEntry): GentleS M:=by
       intro j; rw [Push.PriceCompiler.block_eq h j]; have ht:= le_trans (p ( M.clock.J (j+1))) (h.pays j); have hp:= M.fits.delayed j; exact Real.le_log_iff_exp_le ( Real.log_pos hp ) |>.mpr ((Real.le_log_iff_exp_le (zero_lt_one.trans hp)).mpr ht)
variable (h:Rise B L)
omit h
-- epoch-relative scale
abbrev LogLength (ρ:ι→ℝ):ι→ℝ:=fun i=> Real.log ((ρ i)⁻¹)
abbrev βClock (G:Gauge)(ρ:ι→ℝ):ι→ℝ:= fun i=> G.slopeConstant * LogLength ρ i
lemma radius_clock (g:G.Simple)(a:Tendsto ρ L (𝓝[>]0)) : Rise (βClock G ρ) L:= ( Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp a)).const_mul_atTop (slopeConstant_pos g)
lemma σIdentity (A:Levels G)(i:ℕ)(ρ:ℝ)(h:0<ρ): A.S.scale i - Real.log ρ⁻¹ = Real.log (ρ/A.S.a i):=by rw [Real.log_div h.ne' (A.S.a_pos i).ne', Schedule.scale, log_inv,log_inv]; ring
lemma σStub (A:Levels G)(i j:ℕ): A.S.scale i-A.S.scale j=Real.log (A.S.a j/A.S.a i):=by rw [Schedule.scale,Schedule.scale,Real.log_div ( A.S.a_pos _ ).ne' ( A.S.a_pos _ ).ne', log_inv,log_inv]; ring
lemma τTop (g:G.Simple)(i j:ℕ)(u:M.clock.hatBeta i < M.clock.hatBeta j):i<j:= by by_contra! t; exact not_le.mpr u ( hat_monoM _ g t )
lemma EraT (H:Tendsto (M.clock.hatBeta) atTop atTop)(g:G.Simple)(i j:ℕ): (M.clock.hatBeta i < M.clock.hatBeta j)↔i<j:=by apply Iff.intro (τTop g i j); intro v; exact add_lt_add_right (mul_lt_mul_of_pos_left ( Real.log_lt_log ( by unfold Schedule.a; positivity ) ( by unfold Schedule.a; rw [inv_inv, inv_inv]; exact_mod_cast M.S.den_strict v ) ) (slopeConstant_pos g)) _
include h
lemma polyLeM (u: Wage L (Spread B) 1 A): A =O[L] dollar B:=by obtain ⟨n,v⟩:=u; exact v.trans (by simpa using! polyTo h n)
lemma powerB : dollar B =o[L] B:=by
     have p:( mark B * dollar B)=o[L] ( 1:ι→ℝ):=by rw [mul_comm]; simpa only [pow_one] using power_age h 1
     have v:Tendsto ( mark B ) L (𝓝 0):=by simpa only[pow_zero,one_mul] using mark_sold h 0
     apply isLittleO_of_tendsto' ; · exact (( h.eventually_gt_atTop 0 ).mono fun i hi hz=> False.elim (hi.ne' hz)) -- H mode
     · have hK:Tendsto (fun i=> mark B i*dollar B i*mark B i) L (𝓝 0):= Tendsto.mul ((isLittleO_const_iff (show (1:ℝ)≠0 from one_ne_zero)).mp p) v |>.mono_right ( by rw [mul_zero] ) ;
       refine hK.congr' (( h.eventually_gt_atTop 0 ).mono (fun i hi=>?_)); simp only [mark]; field_simp; rw [Real.sq_sqrt hi.le]; ring
lemma polyLittle (v: Wage L (Spread B) 1 A): A=o[L] B:= ( polyLeM h v ).trans_isLittleO ( powerB h )
variable {w x a:ι→ℕ}
lemma epoch_equiv (p:Epoch L B M w)(q: Wage L (Spread B) 1 (fun i=> M.S.scale (x i)- M.S.scale (w i))): Epoch L B M x:=by
     have ht:= polyLittle h q; have hv: IsLittleO L ((M.clock.hatBeta ∘ x) - M.clock.hatBeta ∘ w) B:= ( ht.const_mul_left G.slopeConstant ).congr_left fun i=> by simp only [Pi.sub_apply]; rw[Function.comp_apply,Function.comp_apply]; unfold Calendar.hatBeta; ring
     exact ( hv.trans_isBigO ( p.isBigO_symm ) ).isEquivalent.trans p
lemma epoch_start (p:B=ᶠ[L] βClock G ρ)(q: Wage L (Spread B) 1 (fun i=> M.S.scale (x i)- LogLength ρ i)): Epoch L B M x:=by
    refine IsLittleO.isEquivalent ( ( ( ( polyLittle h (Wage.unitC M.clock.bar) ).add ((polyLittle h q).const_mul_left G.slopeConstant) ) ).congr' (?_) (.refl ..) )
    · refine p.mono (fun i hi=>?_); change _= M.clock.hatBeta (x i)-B i; rw [hi]; unfold Calendar.hatBeta βClock; ring
-- monotone telescoping and cutoff predecessor.Eclipse L^d.
lemma hull (A:Levels G)(g:G.Simple)(b:GentleS A)(p:Epoch L B A x): Wage L (Spread B) 1 (fun i=> ((A.S.block (x i)).val:ℝ)):=by
    let f(i):= A.clock.hatBeta ( x i ); have hp:=spread_tie h p; apply Wage.rel (q:=Spread f) ; · exact Wage.rel ( show Wage L (Spread B) 1 ( Spread B ) from ⟨1, by simp; exact isBigO_refl _ L ⟩) hp.isBigO
    apply IsBigO.of_bound'; apply Eventually.of_forall; intro i; rw [Real.norm_of_nonneg (by positivity : (0:ℝ)≤ ( A.S.block (x i)).val) ]; have hv :0≤ log (f i):= Real.log_nonneg (A.fits.delayed _).le; refine le_trans (b (x i)) (le_trans (Real.log_le_self hv) (le_abs_self _))
-- closeness Epoch Abel. large fields calendar.Comparisons centers permit Glow estimate all participation in L.Y.
abbrev Glow (A:Levels G)(ρ:ι→ℝ)(B:ι→ℝ)(L:Filter ι)(x:ι→ℕ):Prop:= (fun i=> A.S.scale (x i)-LogLength ρ i)=O[L] Spread B
-- also future Glow²∼ Y².LogB notation.
lemma spread_cost (A:Levels G) (g:G.Simple)(b:GentleS A)(p:Epoch L B A x): (fun i=> ( ( A.S.block ( x i ) ).val:ℝ))=O[L] ( Spread B ) :=by
    have ht:=spread_tie h p; apply IsBigO.trans _ ht.isBigO; refine IsBigO.of_bound' (Eventually.of_forall (fun i=>?_)); rw [Real.norm_of_nonneg (by positivity : (0:ℝ)≤ ( A.S.block (x i)).val) ]; have hz:= Real.log_nonneg (A.fits.delayed (x i)).le; exact le_trans ( b ( x i ) ) (le_trans (Real.log_le_self hz) (le_abs_self ..))
omit h in
lemma stepGrowth (A:Levels G){i j:ℕ}(t:i ≤ j): ( (A.S.block i).val:ℝ)≤ ( (A.S.block j).val:ℝ):=by rw [← A.fits.sameFactor,←A.fits.sameFactor]; apply Nat.cast_le.mpr; exact A.fits.monotoneL (A.fits.mono (Nat.succ_le_succ t))
lemma spread_prev (A:Levels G)(g:G.Simple)(b:GentleS A)(p:Epoch L B A x)(hy:a ≤ᶠ[L] x): (fun i=> ((A.S.block ( a i ) ).val:ℝ))=O[L] ( Spread B ) := by
    apply IsBigO.trans _ (spread_cost h A g b p); refine IsBigO.of_bound' (hy.mono fun i hi=>?_); rw [Real.norm_of_nonneg (by positivity: (0:ℝ)≤ (A.S.block (a i)).val) ]; exact le_trans (stepGrowth A hi) (le_abs_self ..)
lemma stairLimit (A:Levels G)(g:G.Simple)(b:GentleS A)(p:Epoch L B A x)(hy:a≤ᶠ[L]x): (fun i=> A.S.scale ( (a i)+1) - A.S.scale (a i))=o[L] ( Spread B ):=by
    -- want o(Y), log block.Weight. compare log spread budget.
    obtain ⟨C,H,hV⟩:= (spread_prev h A g b p hy).exists_pos; let W:= Spread B
    let Z(i):= C*(Spread B i); have hz:Tendsto Z L atTop:= (y_rise h).const_mul_atTop H
    let F(i):=log ( Z i ); have ht : F=o[L] (Spread B):= IsLittleO.trans_isBigO ((show (log)=o[atTop] (fun i=>i) from by simpa using! (isLittleO_log_rpow_atTop zero_lt_one)).comp_tendsto hz) (isBigO_const_mul_self C _ _)
    simp_rw [ Schedule.scale_succ, add_sub_cancel_left ]; refine IsBigO.trans_isLittleO ?_ ht; refine IsBigO.of_bound' (?_); filter_upwards [hV.bound,( y_rise h ).eventually_gt_atTop 0 ] with i hi hx
    have hn:(1:ℝ)≤ (A.S.block (a i)).val:=by exact_mod_cast Nat.succ_le_of_lt (A.S.block (a i)).property
    rw [Real.norm_of_nonneg (Real.log_nonneg hn)]; apply le_trans (Real.log_le_log (zero_lt_one.trans_le hn) (?_ :((A.S.block (a i)).val:ℝ)≤C*Spread B i)) (le_abs_self _); exact le_trans (le_abs_self _) (by rwa [Real.norm_of_nonneg hx.le] at hi)
lemma next_epoch (A:Levels G)(g:G.Simple)(b:GentleS A)(p:Epoch L B A x) : Epoch L B A (fun i=>x i+1):=by
    refine epoch_equiv h p (Wage.ascend (Wage.enroll (stairLimit h A g b p ( Eventually.of_forall fun i=>le_rfl)).isBigO) ⟨1,?_⟩) -- wrong
    simp; exact isBigO_refl _ _
lemma epoch_wave (p:B=ᶠ[L] βClock G ρ)(q: Glow M ρ B L x): Epoch L B M x:=by apply epoch_start h p (Wage.ascend (Wage.enroll q) _); exact ⟨1, by simp; exact isBigO_refl _ L⟩
end YM.SignedWilsonExpansion.Purchases.Schedules

import YM.WilsonCoeffUV.Emit.RentedCapture
import YM.WilsonCoeffUV.Emit.Expense
/-!
# The estimates admit the logarithmic reporting layout

Clocks A used here; soft stop j beyond Λ_b^2; profile/cap m and reporting r;
close analytic gates use smaller scaled ζ than polynomial reserves. Needs only
anchor reached eventually on same Realm and linear zz receipts. Leased schedules
supply both for fixed rank. No asymptotic coupling iteration in this file.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Layout
open Wheel.ScaleS Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost Physical
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Wheel.Flooring
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{E W:Credit}{m b j e:ℕ}
open Ticket
/-- `2+log β̂`, common k conventions. -/
def longLog (A:Levels G)(m:ℕ):=2+Real.log (A.clock.hatBeta m)
lemma long_pos (A:Levels G)(m:ℕ): 2< longLog A m:= lt_add_of_pos_right _ (Real.log_pos (A.fits.delayed _))
lemma spend (A:Levels G)(m:ℕ): Real.exp (zz A m-1)=Real.log (A.clock.hatBeta m):=by simp only [zz]; rw [add_sub_cancel_left,Real.exp_log (Real.log_pos (A.fits.delayed _))]
lemma toward (A:Levels G)(h:G.Simple): Tendsto (longLog A) atTop atTop:= tendsto_atTop_add_const_left _ _ (YM.Multi.Wage.log_tend h A)
lemma betaR (A:Levels G)(g:G.Simple): Monotone A.clock.hatBeta:= fun _ _ h=> add_le_add_right (mul_le_mul_of_nonneg_left (scales A.S h) (slopeConstant_pos g).le) _
lemma monolog (A:Levels G)(g:G.Simple): Monotone (longLog A):= fun i _ h=> add_le_add_right (Real.log_le_log (zero_lt_one.trans (A.fits.delayed i)) (betaR A g h)) _
lemma short_mono (A:Levels G)(g:G.Simple): Monotone (zz A):= fun i _ h=> add_le_add_right (Real.log_le_log (Real.log_pos (A.fits.delayed i)) (Real.log_le_log (zero_lt_one.trans (A.fits.delayed i)) (betaR A g h))) _
lemma tiny_log (A:Levels G)(m:ℕ): zz A m ≤  longLog A m:=by unfold zz longLog; linarith only [Real.log_le_sub_one_of_pos (Real.log_pos (A.fits.delayed m))]
lemma up_snow (A:Levels G)(g:G.Simple)(b:ℕ)(T:Credit): ∀ᶠ m in atTop,T.buy (longLog A m) ≤  snowP A.S b m:=by
    let u:=G.slopeConstant; let B:=A.clock.hatBeta b; let t:=(pur u).prodC T |>.plus (pur B)
    have hp:0< u:= Gauge.slopeConstant_pos g; have he:= (tendsto_atTop_add_const_left atTop (2:ℝ) (YM.Multi.Wage.log_tend g A)).eventually (absorbed t (Real.exp (-1)) (Real.exp_pos _))
    refine he.mono (fun m hm=>?_)
    let x:= longLog A m; have hx:x>2:= long_pos ..; change t.buy x ≤  _ at hm
    have hf:B + T.buy x * u ≤  t.buy x:=by
        rw [add_comm]; apply le_trans _ (Credit.fuel _ _ (by linarith)); rw [Credit.products, mul_comm (T.buy x)]; exact add_le_add (mul_le_mul_of_nonneg_right (pure_goal ..) (zero_le_one.trans (Credit.purchase _ (by linarith)))) (pure_goal ..)
    have hT: t.buy x≤  A.clock.hatBeta m:=by
        refine hm.trans_eq ?_; rw [← Real.exp_add]; dsimp only [Function.comp_apply]; rw [show -(1:ℝ)+(2+Real.log (A.clock.hatBeta m)-1) = _ from show _=Real.log (A.clock.hatBeta m) by ring,Real.exp_log (zero_lt_one.trans (A.fits.delayed _))]
    let U:= snowP A.S b m; have hv: A.clock.hatBeta m=B+U*u:=by unfold B Calendar.hatBeta U u snowP Levels.S; ring
    rw [hv] at hT; exact (mul_le_mul_iff_of_pos_right hp).mp (le_of_add_le_add_left (hf.trans hT))
lemma pace_log (S:Schedule)(m b:ℕ): paceT S m b= Real.exp (snowP S b m):=by unfold snowP; rw [pace_rep]; ring_nf
lemma pact (S:Schedule)(m b:ℕ): Real.log (paceT S m b)=snowP S b m:=by rw [pace_log,Real.log_exp]
-- from fixed λ_b floor
lemma alignedCapture (A:Levels G)(g:G.Simple)(p:Credit)(j:ℕ): ∀ᶠ m in atTop,∀ r:ℝ,1< r→ r≤ p.buy (longLog A m)→ ∃ b, j≤  b ∧ b< m ∧ r≤ paceT A.S m b ∧ paceT A.S m (b+1)< r:=by
   filter_upwards [up_snow A g j p,eventually_ge_atTop j] with m hm v
   intro r f x; let S:= A.S
   have hj: r ≤  paceT S m j:=le_trans (x.trans hm) (by rw [pace_log]; linarith only [Real.add_one_le_exp (snowP S j m)])
   let s:= (Finset.Iic m).filter fun i=>r≤  paceT S m i; have h: j∈ s:= Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr v,hj⟩; let b:= s.max' ⟨_,h⟩; obtain ⟨ht,hp⟩:= Finset.mem_filter.mp (show b∈ s from Finset.max'_mem ..); have he:= Finset.mem_Iic.mp ht; have hz:b ≠ m:=by intro p; rw [p,pace_self] at hp; exact (not_le_of_gt f) hp
   refine ⟨b, Finset.le_max' _ _ h,lt_of_le_of_ne he hz, hp,lt_of_not_ge (fun z=>?_)⟩
   exact (Nat.not_succ_le_self b) (Finset.le_max' _ _ (show b+1∈ s from Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (by omega),z⟩))
lemma firstStop (A:Levels G)(g:G.Simple)(j:ℕ) : ∀ᶠ b in atTop,∃ i, j≤  i ∧ i< b ∧ longLog A b^2≤  snowP A.S i b ∧ snowP A.S (i+1) b <  longLog A b^2:=by
   let T:= Credit.leanC.powC 2
   filter_upwards [up_snow A g j T,eventually_ge_atTop j] with b hb v
   let X:= longLog A b ^ 2; have ht:X≤  snowP A.S j b:=by unfold X; simpa only [T,Credit.power,Credit.lean_cost] using hb
   let f:= (Finset.Iic b).filter fun i=> X ≤ snowP A.S i b; have h: j∈ f:= Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr v,ht⟩; let i:= f.max' ⟨_,h⟩; obtain ⟨ha,hp⟩:= Finset.mem_filter.mp (show i∈ f from Finset.max'_mem ..); have hu:= Finset.mem_Iic.mp ha
   have hx:0< X:=pow_pos (by linarith [long_pos A b]) _; have hw:i≠ b:=by intro p; rw [p, snowP,sub_self] at hp; exact (not_le_of_gt hx) hp
   refine ⟨i,Finset.le_max' f _ h,lt_of_le_of_ne hu hw,hp,lt_of_not_ge (fun p=>?_)⟩; apply Nat.not_succ_le_self i; exact Finset.le_max' _ _ (show i+1∈ f from Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (by omega),p⟩)

structure Windows (S: Levels G)(a m b j:ℕ)(r:ℝ): Prop where
   atBase : a ≤  j
   soft : j <  b
   capture : b <  m
   firstC : r ≤  paceT S.S m b
   lastC : paceT S.S m (b+1)< r
   firstS : longLog S b^2 ≤  snowP S.S j b
   lastS : snowP S.S (j+1) b <  longLog S b ^2
lemma rooms (A:Levels G)(g:G.Simple)(p:Credit)(a:ℕ): ∀ᶠ m in atTop, ∀ r:ℝ,1< r→ r≤ p.buy (longLog A m)→ ∃ b j,Windows A a m b j r:=by
   obtain ⟨i,h⟩:= eventually_atTop.1 (firstStop A g a); filter_upwards [alignedCapture A g p i] with m hm
   intro r hr hx; obtain ⟨b,z,l,hb,f⟩:= hm r hr hx; obtain ⟨j,p,w,u,x⟩:= h b z; exact ⟨b,j,p,w,l,hb,f,u,x⟩
end YM.WilsonCoeffUV.Layout

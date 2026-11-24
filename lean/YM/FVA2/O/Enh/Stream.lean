import YM.FVA2.O.Enh.Rain
/-!
# Formal costs through power series algebra
 Multiplying by finite power functions and absorbing coupling-log variation.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Enh
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score
variable {G:Gauge}{ I J E:Type }{a b:ℝ}{n m:ℕ}
abbrev ChargeP (d:ℕ)(a:ℝ)(f:I→ℝ→ Cn): Prop:= ∀ i<d,Rain a (fun k t=> coeff i (f k t))
namespace ChargeP
variable { f g h:I→ℝ→ Cn }
lemma unit : ChargeP n a (fun (_:I) (_:ℝ)=> (0:Cn) ):= by intro i _; simp only [map_zero]; exact Rain.nil _
lemma fixed (x:Cn): ChargeP n 0 (fun (_:I) _=> x ):= fun _ _=> Rain.fixed _
lemma pull (he: ChargeP n a f)(ξ:J→I): ChargeP n a (f∘ ξ):= fun i hi=> (he i hi).pull _
lemma move (hp:ChargeP n a f)(he:m≤n): ChargeP m a f:= fun _ hv=> hp _ (Nat.lt_of_lt_of_le hv he)
lemma grow (hp:ChargeP n a f)(he:b≤a): ChargeP n b f:= fun _ v=> (hp _ v).size he
lemma plus (hp:ChargeP n a f)(h: ChargeP n a g): ChargeP n a (fun i t=> f i t+g i t):= by intro i hi; simp_rw [map_add]; exact (hp i hi).plus (h i hi)
lemma sub (hp:ChargeP n a f)(h:ChargeP n a g): ChargeP n a (fun i t=> f i t-g i t):= by intro i hi; simp_rw [map_sub]; exact (hp i hi).minus ( h i hi )
lemma joint (hp: ChargeP n a f)(h:ChargeP n b g): ChargeP n (a+b) (fun i t=> f i t*g i t):= by
    intro i hi; simp_rw [coeff_mul]; apply Rain.sum; intro j hj; have h' := Finset.mem_antidiagonal.mp hj; exact ( hp j.1 (by omega) ).mul ( h j.2 (by omega) )
lemma times (hp: ChargeP n 0 f)(h:ChargeP n b g): ChargeP n b (fun i t=>f i t*g i t):= by simpa only [zero_add] using joint hp h
lemma sum (s:Finset J){f:J→ I→ℝ→ Cn}( h:∀ i∈s,ChargeP n a ( f i ) ): ChargeP n a (fun i t=> ∑ j∈s,f j i t):= by intro i hi; simp_rw [map_sum]; exact Rain.sum _ fun j hj=> h j hj i hi
lemma product (s:Finset J){f:J→ I→ℝ→ Cn}(h:∀ i∈s,ChargeP n 0 ( f i )): ChargeP n 0 (fun i t=>∏ j∈s,f j i t):= by
    classical induction s using Finset.induction_on with| empty=> simp only [ Finset.prod_empty ]; exact fixed _ | insert i s hi ih=> simp only [Finset.prod_insert hi]; exact times (h _ ( Finset.mem_insert_self .. )) ( ih fun j hj=> h j (Finset.mem_insert_of_mem hj) )
lemma power (hp:ChargeP n 0 f)(k:ℕ): ChargeP n 0 (fun i t=> f i t ^ k ):= by induction k with| zero=> simp only [ pow_zero ]; exact fixed _| succ i ih=> simp_rw [ pow_succ ]; exact times ih hp
lemma Pact (hf:ChargeP n a f)(he:ChargeP n 0 g)(hx:∀ i t,Rooted (g i t)): ChargeP n a (fun i t=> ( f i t ).subst ( g i t )):= by
    intro i hi; have h q t: coeff i ( (f q t).subst (g q t))=∑ j∈Finset.range (i+1), coeff j ( f q t )*coeff i (g q t^j):= FPS.coeff_substituted _ (( coeff_zero_eq_constantCoeff_apply _ ).symm.trans ( hx q t )) _ -- signature
    simp_rw [h]; exact Rain.sum _ fun j hj=> (hf j (by simp only [ Finset.mem_range ] at hj; omega)).wig ( he.power j i hi )
lemma constants {f:I→ℝ→ ℂ}(hf:Rain a f): ChargeP n a (fun i t=> PowerSeries.C ( f i t )):= by
    intro i hi; simp_rw [coeff_C]; by_cases h:i=0; · simpa [h] using! hf
    simp only [ if_neg h ]; exact Rain.nil _
variable {B:ℝ→Cast G}{F:ℝ→ Cn}
lemma town (h:Town B)(p q:Q G): ChargeP n 0 ( fun (_:I) t=> cue ( B t ) p q ) := by
    unfold cue; by_cases hv:q.h=p.h; simp only [ dif_pos hv ]; exact fun i _=> Rain.rhythm ( h _ _ _ i ); simp only [ dif_neg hv ]; exact unit
lemma extreme (h:Town B)(p v:Scan G m): ChargeP n 0 (fun (_: I) t=> play ( B t ) p v ):= product _ (fun i _=> town ( I:=I ) h ( p i ) ( v i ))
lemma clean (h:Meter.Clear F): ChargeP n 0 (fun (_:I) t=>F t):= fun i _=> Rain.rhythm ( Rhythm.unit.mpr ( h i ) )
end ChargeP
lemma feeV : ChargeP n a (fun (_:I) (t:ℝ)=> PowerSeries.C ( Score.fee t a )):= ChargeP.constants Rain.all_fee
lemma reflectV : ChargeP n (-a) (fun (_:I) t=> PowerSeries.C ( Score.fee (-t) a )):= by simp_rw [ show ∀ t:ℝ, Score.fee (-t) a=_ from fun t=> (by unfold Score.fee; simp [ neg_neg ] : Score.fee (-t) a=Score.fee t (-a)) ]; exact feeV
end YM.FVA2.O.Enh

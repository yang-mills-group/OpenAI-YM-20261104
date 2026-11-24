import YM.MS.Dock.Make
/-!
# Remove homogeneous ambiguity after implicit Cycle: Uniqueness full (unmarked action independent even of UV extension outside z-near? but off Course flow imposed)
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dock
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F Z J L:Flats G}{K U:Mob G}{f g p q:Coat G}{b c:Bool}{t v r:ℤ}{n h ℓ:ℕ}{i:ℂ}
lemma common (hx: Pact X Y)(hv:Pact F J): Pact (X+F) (Y+J):= fun i=> ( hx i).add (hv i)
lemma pact_union (h:Pact F X)(hm:Pact F Y): Pact X Y:= fun i=> ( (h i).symm.trans (hm i))
lemma uniq (h:Joint n (step0 G X) X 0 p)(ht:ClockD b t r X): Pact X 0∧p=0:= by
   suffices hv : ∀ k:ℕ,∀ r:ℤ, r≤(k:ℤ)→ ClockD b t r X→Pact X 0∧p=0 from hv r.toNat _ (by omega) ht; clear ht;
   intro k; induction k using Nat.strong_induction_on with
   | h k ih=>
      intro r hR hX; obtain hv :=mine hX h.toll; by_cases he:r<2; · exact robe (h.via (pact0 ⟨_,(by omega:r-2<0), clockCap hv.eye ⟩))
      obtain ⟨F,q,H,hK,hp⟩:= run hv (f:=0) (fun _=> Home.zero _) Cap0.zero; obtain ht:= uniqueK H h (fun _=> EventuallyEq.rfl) EventuallyEq.rfl;
      exact ih (k-1) (by omega) (r-2) (by omega) ( clockWind hK ht.1)
-- linear compare strong rolling Cap
lemma clock_sub (h:ClockD b t r F)(he:ClockD b t r Y): ClockD b t r (F-Y):= fun i=> (h i).sub (he i)
lemma super (hx: Joint h (J+step0 G X) X f p)(hv: Joint h (L+step0 G Y) Y g q)(he:Pact L J)(hp:Spotty g f)(hX:ClockD b t r X)(hY:ClockD b t v Y): Pact X Y∧p=q:= by
    obtain h:= hx.sub ((hv.via (F:=J+step0 G Y) (common he (fun _=>EventuallyEq.rfl))).VU hp); rw [sub_self (a:=f),show J+step0 G X-(J+step0 G Y)= _ from (calc
       _= step0 G X-step0 G Y:= by abel
       _=step0 G (X-Y):= (map_sub ..).symm )] at h; obtain ⟨H,F⟩:= uniq h (clock_sub (clockTrans hX (le_max_left r v)) (clockTrans hY (le_max_right r v))); exact ⟨pact_sub_zero H,sub_eq_zero.mp F⟩
-- Pact through Tree, noncons ok. specialize via pair-expansion and disappear delta's. uses *linear exact explosion*. 
lemma glare (h:Pact X 0)(u:Oceans.Pair G): Pact (explode (tapeB u) X F) 0:= by
   have he:= took h; let E:=tapeB u; intro j; apply he.mono; intro i hi; rw [explodeL]; unfold Finsupp.sum; simp only [ Finset.sum_apply',Finset.sum_apply]; refine Finset.sum_eq_zero fun a ha=> Finset.sum_eq_zero fun b hb=>?_; rw [Finsupp.single_apply]; split; swap; rfl; change u (X a i) (F b i)=_; rw [hi,Finsupp.zero_apply,Pi.zero_apply,map_zero]; rfl -- E unfold not possible? hi d unification target ζ Apply
lemma flare (h:Pact F 0)(u:Oceans.Pair G): Pact (explode ( tapeB u) X F) 0:= by
   have he:= took h; intro j; apply he.mono; intro i hi; rw [explodeL]; unfold Finsupp.sum; simp only [ Finset.sum_apply',Finset.sum_apply]; refine Finset.sum_eq_zero fun a ha=> Finset.sum_eq_zero fun b hb=>?_; rw [Finsupp.single_apply]; split; swap; rfl; change u (X a i) (F b i)=_; rw [hi,Finsupp.zero_apply,Pi.zero_apply,map_zero] -- hi d unification target ζ Apply
lemma coat_sub (h:Pact X F): Pact (X-F) 0:= fun i=> (h i).mono fun _ h=> sub_eq_zero.mpr h
lemma pair_pact (U:Rip G)(h:Pact X Y)(he:Pact L Z) : Pact ( TreeN U X L) (TreeN U Y Z):= by
   have hv:=glare (F:=L) (coat_sub h) (squad U); have hm:=flare (X:=Y) ( coat_sub he) (squad U); unfold TreeN; apply pact_sub_zero; rw [show explode (tapeB (squad U)) X L- explode (tapeB (squad U)) Y Z=_ from (calc
       _=_+_:= Eq.symm (show explode (tapeB (squad U)) (X-Y) L+ explode (tapeB (squad U)) Y (L-Z)=_ from by rw [map_sub,map_sub,LinearMap.sub_apply]; abel))]; simpa only [add_zero] using common hv hm
end YM.MS.Dock

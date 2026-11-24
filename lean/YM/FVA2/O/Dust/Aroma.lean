import YM.FVA2.O.Dust.Holy
/-!
# Costing the full product (at negative log times)

`resin`: forming the simple product from the singleton data. `aroma` for its costs,
`sents` for pricing the full multi-insertion difference from that, with **arbitrary** power
decay under the stated geometric hypotheses (`Sweep` in `Holy`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Cool
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Osc MS.Osc.Snap MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real MS.Tide
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff Serve Rake.Geo Vane Actors Fuse Job.Belt
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type}[LinearOrder W]{F H:Rake.Site G I}{p a b:I→ QP}{q:ℤ}{P:Geo I}{B:Deck G}{K:Booked B}{M:MS_Data G K}{X:Rake.Dance G I W}{S:Finset W} {x: Position W I}{U:W→Rake.Label B}
def wax (X:Rake.Dance G I W): Rake.Dance G I W := fun S=> if S.card=1 then X S else 0
abbrev resin (x: Position W I)(X:Rake.Dance G I W):= Meal ( wax (untap x X) )
omit [LinearOrder W] in
lemma gazeU : nav M P.η (glaze G I).unit=0:= by
    suffices he : (nav M P.η) (glaze G I).unit=0 from he -- remove
    funext n; unfold nav; simp only [LinearMap.add_apply,Pi.add_apply,promised, paired ]; -- too much?
    have hz i : (glaze G I).unit i= if i=0 then (hori G I).unit else 0 := by unfold glaze Actors.stack; dsimp only; unfold SplitP.refineV; congr! 1 -- classical
    change (both G I).J _+( ∑ i∈antidiagonal n, (both G I).C (Lives.gather M P.η i.1) ( (glaze G I).unit i.2 ))=_; rw [Finset.sum_eq_zero]; swap
    · intro i _; rw [hz i.2]; split; · exact funext fun k=> funext fun t=> clearT _ _
      rw [map_zero]
    rw [add_zero,hz]; split; swap; · exact map_zero _
    funext i s; change (Q G 0).raise (coin (1:ℂ)) + Heat.orbit ( lineB G s ) planeF (coin (1:ℂ)) = (0:Law G); rw [show (Q G 0).raise _=0 from Eq.trans (congr_arg _ Lifting.coin_hit) (Local.MatrixLet.no _),zero_add,finite_cc planeF (rB.pays Geo.Coherent Wallet.cash)]; funext l; unfold Ccy; simp [coin]
omit [LinearOrder W] in
lemma Toe (h:Banks F 0): Touch G I F (glaze G I).unit=0:= by have hm:= touch_graft (hedge h) ( (glaze G I).holds ) ( Fuse.unitC ( G:=G ) ( I:=I ) ); let V:=(glaze G I); change Touch G I F ( V.core V.unit V.unit ) = V.core _ _ + V.core _ _ at hm; rw [ V.identityK,V.identityR,V.identityK ] at hm; exact ( add_right_inj ( Touch G I F V.unit ) ).mp (by rw [add_zero]; exact hm.symm)
lemma resin_nil : resin x X ∅= (glaze G I).unit:= Puff.Stencil.simple_E (B:=SplitP.marked W) _ _ (by simp only [Happy,wax,SplitP.marked]; rw [if_neg]; simp) -- args inspect
omit [LinearOrder W] in
lemma wax_guard (h:∀ s,Banks (X s) 0)(s:Finset W): Banks (wax X s) 0:=by unfold wax; split; exact h s; exact fun _=> Bank.zero
lemma raw_wax (h:∀ s,Banks (X s) 0){i:W}(he:i∉S): Meal (wax X) (insert i S)= bond G I (X {i}) (Meal (wax X) S) := by
    obtain ht:(glaze G I).Cheer (SplitP.marked W) (wax X) (insert i S)=_:= Puff.Stencil.cheers (glaze G I) (hx:=fun s=> hedge ( wax_guard h s )) ( hp:=fun s h=> if_neg (show s.card≠1 from h) ) _ i he; change _= (glaze G I).core _ _; rw [ show X {i} = wax X {i} from (by simp [wax]) ]; exact ht
lemma headU (h:DOrd K P M U x X)(i:W): untap x X {i}=swing G (x i) ( rowM P M ( U i )):= by unfold untap; rw [h.2.1 ]; simp [ rootX ]
-- U not uniform compacts -> first per regular. 
variable (h:Mesh P x)(ht:P.θ=0)(hx:DOrd K P M U x X)(he:∀ i,Fixed (x i))
include h hx he ht
lemma gustS : Stageable P (untap x X S):= fun i=> untitled ( royalU ( cinder ht h hx i|>.1 ) ) ( RootFixed he )
lemma sents (s:Finset W) : Sweep P (plenum x X s - resin x X s):= by
    let F:=untap x X; have hu(S):=gustS ( S:= S ) h ht hx he -- order args
    refine dust_meal (P:=P) (X:=F) ?_ hu ?_
    · intro s; by_cases hP:s.card=1; · rw [Pi.sub_apply, wax,if_pos hP,sub_self]; exact Sweep.unit
      rw [ Pi.sub_apply,wax,if_neg hP,sub_zero ]; obtain hz|hz:=s.eq_empty_or_nonempty; · rw [hz,show F ∅=0 from ( by unfold F untap; rw [hx.1,map_zero] ) ]; exact Sweep.unit
      exact fun k=> ( cinder ht h hx k |>.2 ( by obtain hp:=Finset.card_pos.mpr hz; omega ) ).fixed ( RootFixed he )
    intro s; unfold wax; split; exact hu s; exact fun _=> Fairy.zero
lemma aroma (s:Finset W): Stageable P (resin x X s):= by
    induction s using Finset.induction_on with | empty=> rw [ resin_nil ]; exact Arc_zero| insert i s hi ih=> rw [resin,raw_wax (X:=untap x X) (fun s k=> bankTilt ( solitude hx (world_price h hx) k )) hi ]; exact castW ( gustS h ht hx he ) ih
end YM.FVA2.O.Cool

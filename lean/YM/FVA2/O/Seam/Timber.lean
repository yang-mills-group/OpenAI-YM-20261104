import YM.FVA2.O.Seam.Bands
/-!
# The two types of multi-mark inputs in the FAR estimate

`woods`: simple unanchored products (`resin`); `thicket`: full products (`plenum`),
including correlations between marks. Keep the parameterized MS estimates on them
before using the separated-geometry pricing in subsequent files.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo O.Price O.Fuse
open scoped Topology ContDiff Interval
variable { G:Gauge } { α W I : Type } { B: Deck G } {K:Booked B}{M:MS_Data G K}{P:Geo I} {s:Finset W}{x: Position W I}{R:W→ Label B}{u:Label B}{p:I→ QP}{S:Home α I}{q:ℤ}{n:ℕ}{η:I→ℝ} {F:T ( Glade G I )}
abbrev singletonM (P:Geo I)(M:MS_Data G K)(p:I→QP)(u:Label B): T ( Glade G I ):= swing G p ( rowM P M u )
abbrev height (R:W→Label B)(s:Finset W): ℕ:= ∑ i∈s,( R i ).h
lemma Certified_single (u:Label B): Certified ( singletonM P M p u ) M P.η 0 := snake ( Certified.first u.item )
lemma priceField (hp: liveP S P.η) : Latch.Lease false false S.toScale (sendT S ( rowM P M u n )) (Cool.stamp S.toScale (-( u.h:ℤ ))):= ageM hp (M.markOK u.h u.item)
lemma priceF (hp:liveP S P.η)(n:ℕ): totalT S (singletonM P M p u n) (Cool.stamp S.toScale (-(u.h:ℤ))) false:= FormP.chair _ (from_cost ( priceField ( M:=M ) ( n:=n ) ( u:=u ) hp ))
lemma priceT (hp: liveP S P.η): Calm S P ( singletonM P M p u ):= fun i=> ⟨_,FormP.stays ( priceF hp i ) ( TarLow ( q:=- (u.h:ℤ) ) ( by omega ) )⟩
lemma totalUnit : ∀ n:ℕ,totalT S ( ( glaze G I ).unit n ) 1 false:= by
    intro n; change totalT S (Puff.SplitP.refineV Puff.SplitP.nat _ n) _ _; unfold Puff.SplitP.refineV; split; swap; · exact FormP.unit (fun _=>zero_le_one)
    intro E _ _ w hx; unfold Tax Chart; rcases w with _|⟨i,w⟩; · exact Cost.of_le fun i p _=>by simp only [ Qbud,pitch,fieldDim,List.map_nil,List.sum_nil,zpow_zero,one_mul,Pi.one_apply ]; exact ( norm_one ( α:=ℂ ) ).le
    exact Size.rest fun k _ _=> pos_nn ( x:=1 ) (fun _=>zero_le_one) S.toScale k
variable [LinearOrder W]
abbrev woods (P:Geo I)(M:MS_Data G K)(x:Position W I)(R:W→Label B):= resin x (patchD P M x R)
abbrev thicket (P:Geo I)(M: MS_Data G K)(x:Position W I)(R:W→Label B):= plenum x (patchD P M x R)
abbrev rootT (P:Geo I)(M:MS_Data G K)(x:Position W I)(R:W→Label B)(s:Finset W):= bond G I ( woods P M x R s )
lemma W_nil : woods P M x R ∅=( glaze G I ).unit:= resin_nil
lemma R_nil : rootT P M x R ∅ F=F:= by unfold rootT; rw [W_nil]; exact ( glaze G I ).identityK F
lemma firm (h:separable x): Certified ( thicket P M x R s ) M P.η 0 := advance_r h ( serves h )
variable ( h:separable x )
include h
lemma beds (s:Finset W): Banks (untap x ( patchD P M x R ) s) 0:= fun n=> bankTilt ( solitude ( serves h ) ( a_warm h ( serves h ) ) n )
lemma W_step (i:W)(he:i∉s): woods P M x R (insert i s)= bond G I (singletonM P M ( x i ) ( R i )) (woods P M x R s):= by unfold woods resin; rw [ raw_wax ( beds ( M:=M ) ( P:=P ) ( R:=R ) h ) he, headU ( M:=M ) ( P:=P ) ( serves h ) ]
lemma R_step (i:W)(he:i∉s): rootT P M x R (insert i s) F= bond G I ( singletonM P M ( x i ) ( R i ) ) (rootT P M x R s F) := by unfold rootT; rw [ W_step h i he ]; exact (glaze G I).star_a ..
lemma W_bank (s:Finset W): Banks ( woods P M x R s ) 0:= eating fun s=> wax_guard (beds h) s
lemma R_bank (hp: Banks F q)(s:Finset W): Banks (rootT P M x R s F) q := ( zero_add q ) ▸ joins ( W_bank h s ) hp
lemma W_pay (hp: liveP S P.η)(n:ℕ): totalT S ( woods P M x R s n ) (Cool.stamp S.toScale ( -(height R s:ℤ) )) false:= by
    induction s using Finset.induction_on generalizing n with
    | empty=> rw [W_nil,height, Finset.sum_empty,Nat.cast_zero,neg_zero,show Cool.stamp S.toScale 0=1 from ( by ext; simp [Cool.stamp] ) ]; exact totalUnit n
    | insert i s hi ih=>
        rw [ W_step h i hi,height, Finset.sum_insert hi,Nat.cast_add, neg_add' ]; unfold height at ih; rw [ sub_eq_add_neg, stampA ]; exact bond_le ( k:=n+1 ) (fun i' _=> priceF hp i') (fun i' _=> ih i') (fun _=>posS _|>.le) (fun _=>posS _|>.le) (by omega)
lemma Calm_W ( hp: liveP S P.η )(s:Finset W): Calm S P ( woods P M x R s ):= fun n=> ⟨_,FormP.stays (W_pay h hp n) ( TarLow ( q:=- (height R s:ℤ) ) (by omega))⟩
end YM.FVA2.O.Seam

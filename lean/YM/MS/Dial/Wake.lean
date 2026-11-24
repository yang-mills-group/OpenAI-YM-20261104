import YM.MS.Dial.Stir
/-!
# Negative time domination in continuum frame.Purpose: separated continuity; also grants actual PT regulator statements on sequences of profile samples converging to fixed physical positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Vane -- alias
open scoped Topology ContDiff
variable {I W E:Type} {G:Gauge} {v t:ℝ}{a b:ℤ}{l:Filter I} {r:ℕ}
set_option quotPrecheck false
local notation "Υ" => east ( frameF I v ) false
local notation "Ω"=> ( Υ ).price
open Wire Belt
variable {F H:Glade G I}{m:I→QP}
variable {p:I}
local notation "R"=> frameF I v
local notation "D"=> constantP G I (PlanetD G)
variable [LinearOrder W] {B:Deck G}{M:Booked B}{b:MS_Data G M}(X:W→Label B){x:Position W I}{K:Rake.Dance G I W}
local notation "m0"=> (fun (_:I)=>planeF)
local notation "Sκ"=> approach (frameF I v) b
variable (h: Mesh (frameF I v) x)(ht:DOrd M (frameF I v) b X x K) {s:Finset W}{n:ℕ}
include h ht
lemma source (hs:2≤s.card) : Came R false (Src x m0 D D Sκ K s n):= by
    let S:= Rake.builder b h X; unfold Src multi lonely; obtain hx: CabinF (K:=Υ) (birthTar R) ( ∑ i∈ Domain.paths n 0, expJ D ( Sκ (n-i) ) ( K s i )) ∧ collect (∑ i∈ Domain.paths n 0, expJ D ( Sκ (n-i) ) ( K s i ) ):= seamount ( fun i hi=> cone S.ground ( emerged S ht hs i ) ( S.energy ( n-i ) ( by obtain hv: i<n:= (Finset.mem_Ico.mp hi).2; omega ) ) );
    have he: Came R false (∑ i∈ picks s, ∑ j∈ antidiagonal n, regionC m0 ( rootX x i - rootX x s ) D ( K i j.1 ) (K (s\i) j.2 )):= by
        apply seamount; intro i hi; apply seamount; intro j hj; obtain ⟨r,hr⟩:= tip0 S ht ( n_small hi |>.2.1 ) ( n:=j.1 ); obtain ⟨q,hq⟩:= tip0 S ht ( n_small hi |>.2.2.1 ) ( n:=j.2 ); exact Geo.touch S.ground ( Rake.space h hi ) hr hq
    exact ⟨ hx.1.add he.1, collect_p hx.2 he.2 ⟩
omit h ht
lemma CameZ (hp:Came R false F): Came R false ( sailP m0 D F ):= by
   have he := ( ready ( K:=D ) _ ( masterD G I R ) ); obtain ⟨n,hn⟩:= hp.2; exact ⟨ he.invoke F hp.1, n, Rake.behind ( Rake.Duty.fee he.motor hn ) (by omega) ⟩ -- args inspect
variable [l.IsCountablyGenerated](hv:∀ i:W,tend l p ( x i ))
local notation "C"=> rhythm ( p:=p ) ( l:=l )
omit hv
lemma washT (hp: C F) : C (expJ D ( Sκ n ) F):= by
    intro s hs w; let A:= approach R b n; exact Milk.centerS _ ( sense_atRight (p:= Landau.parity ) ( PlanetD G s ) ( A p s ) |>.reaches w ) ( hp s hs ) -- arg order.fix
lemma washSum (T:Finset W){K:W→Glade G I}(hx:∀ i∈T,rhythm ( l:=l ) ( p:=p ) ( K i )): C (∑ i∈T,K i):= by intro s hs w; unfold tend; simp_rw [ Finset.sum_apply ]; exact tendsto_finsetSum _ (fun i hi=> hx i hi s hs w)
include h ht hv
lemma Wake (T: Finset W) (n:ℕ): C ( K T n ):= by
    let S:= Rake.builder b h X; induction T using Finset.strongInductionOn generalizing n with| _ T ih=>
       obtain H|H:= T.eq_empty_or_nonempty; · subst T; rw [ht.1]; exact fun _ _ _=> tendsto_const_nhds
       by_cases hm : T.card≥2; swap; · obtain ⟨s,hs⟩:= Finset.card_eq_one.mp ( show T.card=1 from by obtain hv:= Finset.card_pos.mpr H; omega ); rw [ hs,ht.2.1 ]; exact fun _ _ _=> tendsto_const_nhds
       induction n using Nat.strong_induction_on with| h n hi=>
        let U:= K T n; let L:= Src x m0 D D Sκ K T n; let Q:= sailP m0 D U+ L; have he:= emerged S ht hm n; obtain hx:= source X h ht ( n:=n ) hm; have htQ:= CameZ he; have hpQ: Came R false Q:= ⟨htQ.1.add hx.1, collect_p htQ.2 hx.2 ⟩; have h80:C L:= by
           intro s hs w; simp only [L,Src,multi,lonely,Pi.add_apply,Finset.sum_apply ]; apply Tendsto.add; · exact tendsto_finsetSum _ (fun i h=> washT ( b:=b ) ( v:=v ) ( hi _ ( Finset.mem_Ico.mp h|>.2 ) ) s hs w) -- n:= infer
           refine tendsto_finsetSum _ (fun i hy=> tendsto_finsetSum _ (fun j hj=> ?_)); obtain hQ:= n_small hy; obtain ⟨v0,hV⟩:= tip0 S ht ( n:=j.1 ) hQ.2.1; obtain ⟨k,hK⟩:=tip0 S ht ( n:=j.2 ) hQ.2.2.1; refine joins0 hV.2.2 hK.2.2 ( m:=rootX x i-rootX x T ) ?_ ( ih i hQ.1 _ ) ( ih _ hQ.2.2.2 _ ) s hs w; apply Tendsto.sub; rw [ rootX,dif_pos hQ.2.1 ]; exact hv _; rw [ rootX,dif_pos H ]; exact hv _
        have he':= ht.2.2 T hm n; obtain hs : K T n=river Q:= he'.2.2; obtain ⟨k,hk⟩:= he.2; intro t ht w; suffices hx : ∀ (u:ℕ) (w:Legs (Lane4 G)) t,t ≤ 0 → ( k < u+w.length )→ tend l p (fun i:I=>K T n i t w) from hx (k+1) w t ht ( by omega )
        intro u; induction u with
        | zero=> intro w t ht hu; unfold tend; simp_rw [ show ∀ i, K T n i t w=0 from fun i=> hk i t w ( by omega ) ]; exact tendsto_const_nhds
        | succ u uh=> intro w t ht hu; rw [hs]; exact Dial.pastH hpQ ht w ( fun y hy=> Tendsto.add ( loopT hy w he (fun l hv=> uh l _ hy (by omega)) ) ( h80 y hy w ) )
end YM.MS.Dial

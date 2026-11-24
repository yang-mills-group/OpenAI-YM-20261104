import YM.FVA2.Extras.Passage
/-!
# Construct `Field` estimates

`aligns`: suppression of the difference between the `plenum` and `resin`,
for `Teams` on the specified separated geometry. See `P.θ=0` etc.
hypotheses. Auxiliary to the optional extension to extra `Forth` fields,
see `Extras/Result`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
open Job.Belt Rake.Geo O.Hue O.Fuse O.Cool

variable {I Gv W: Type}[LinearOrder W] {G:Gauge}{b d:ℤ}{B:Deck G}{K:Booked B}{M:MS_Data G K}{P:Geo I}{x:Position W I}{Q:W→T (Glade G I)}{S:Finset W}{X:Rake.Dance G I W}
local notation "Λ0"=> (fun _ : I=> lineA G)
local notation "K0"=> Geo.constantP G I (PlanetD G)
local notation "m0"=> (fun _:I=> planeF)
abbrev Survey (P:Geo I)(M:MS_Data G K)(Q:W→T (Glade G I))(x:Position W I) : Prop:= ∀ i, Field P M (x i,Q i) 0
abbrev Teams (P:Geo I)(M:MS_Data G K)(Q:W→T (Glade G I))(x:Position W I)(X:Rake.Dance G I W) := Fields x m0 Λ0 Λ0 (Lives.gather M P.η) Q X
variable (hW:Survey P M Q x)
open MS.Puff MS.Puff.Actors
include hW
lemma units (h:Teams P M Q x X)(hx:∀ s k,Warm (X s k) false): Banks ( X S ) 0:= by
    induction S using Finset.strongInductionOn with| _ s ih=>
    by_cases hp: s.Nonempty; swap; · rw [Finset.not_nonempty_iff_eq_empty.mp hp, h.1]; exact fun _=> Bank.zero
    by_cases hs: s.card≥2; swap
    · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from by obtain he:= Finset.card_pos.mpr hp; omega); rw [h.2.1]; exact ( hW i ).1.life
    intro k; induction k using Nat.strong_induction_on with| h k IH=>
    obtain ⟨hC,hQ,hY⟩:= h.2.2 s hs k; let A:= Lives.gather M P.η; let V:= multi m0 x Λ0 Λ0 A (X s) X k s; have he : Bank V 0:=(Bank.all_fin _ (fun i hi=>( (plenary M) (k-i) ).X (IH i (( Finset.mem_Ico.mp hi ).2 )))).add ( Bank.all_fin _ (fun i hi=> Bank.all_fin _ (fun j _=> point (ih i ( n_small hi|>.1 ) j.1) (ih (s\ i) ( n_small hi|>.2.2.2 ) j.2) )) ); refine triple (hx s k) he ⟨ hC,?_,?_⟩
    · obtain hv: (both G I).P ( X s k )= _:= spine ( hF:=hx s k ) realityA; dsimp only; rw [hv]; exact hQ
    obtain hv : (both G I).P ( X s k )=_:= spine (hx s k) realityA; dsimp only; rw [hv]; exact hY
section
variable (h:Teams P M Q x X)(hx:∀ s k,Warm (X s k) false)
include h hx
lemma repletes : ∀ n, Velocity ( untap x X S n ) ((helm M P.η (untap x X S) +∑ i∈ picks S, Share G I (untap x X i) (untap x X ( S\ i ))) n) := by
    by_cases he:S.card<2
    · obtain hs|⟨i,rfl⟩:= ( by by_cases hv:S=∅; exact Or.inl hv; exact Or.inr ( Finset.card_eq_one.mp (by have h:0< S.card:= Finset.card_pos.mpr ( Finset.nonempty_iff_ne_empty.mpr hv ); omega) ) : S=∅ ∨ ∃ i:W,S={i} )
      · subst S; rw [show picks (∅:Finset W)=∅ from ( by ext; simp [ picks ] ), show untap x X ∅=0 from ( by unfold untap; rw [h.1,map_zero] ) ]; simp only [map_zero, Finset.sum_empty, add_zero]; exact fun _ _ _ _=> hasDerivAt_const ..
      · rw [show picks ({i}: Finset W)=∅ from Finset.eq_empty_iff_forall_notMem.mpr fun k hk=> clips (by simp) hk,Finset.sum_empty,add_zero]; unfold untap; rw [h.2.1]; exact (snakeV (p:=rootX x {i}) ( hW i ).1).vital
    have hm:= units hW h hx ( S:=S ); intro k; obtain ⟨h₁,h₂,h₃⟩:= h.2.2 S (le_of_not_gt he) k; let F:=Lives.gather M P.η; let H:=∑ i∈ picks S,∑ j∈ antidiagonal k, regionC m0 (rootX x i-rootX x S) Λ0 (X i j.1) ( X (S\i) j.2 ); let Y:= helm M P.η (X S) k+H; let T:= rootX x S; obtain hY : sailP m0 Λ0 (X S k)+ multi m0 x Λ0 Λ0 F (X S) X k S= Y:= Eq.trans (Eq.symm (add_assoc _ _ _)) (congr_arg (· + H) ( hel_core' k hm ).symm); change X S k=river ( sailP m0 Λ0 ( X S k )+multi m0 x Λ0 Λ0 F (X S) X k S ) at h₃; rw [hY] at h₃; change Job.train false ( sailP m0 Λ0 ( X S k ) +multi m0 x Λ0 Λ0 F (X S) X k S ) at h₂; rw [hY] at h₂
    have hh : Bank H 0:= Bank.all_fin _ (fun i hi=> Bank.all_fin _ (fun j hj=> point ( units hW h hx _ ) ( units hW h hx _ )))
    have he':Bank Y 0:= ( (( plenary M ).lives hm) k ).add hh
    have hVV : Velocity (X S k) Y:= by rw [h₃]; intro i t w; rw [funext (fun t=> swamp h₂ i t 0 (v:=w) (fun x=>Bool.noConfusion x))]; exact ( hfun ( he'.cross.walk _ _ (fun x=>Bool.noConfusion x) ) t).const_add _
    have hv:= velTilt (p:=T) hVV; change Velocity _ ((helm M P.η (swing G T (X S))+ _) k); rw [ ← helion (hx S), Pi.add_apply ]; suffices he : (∑ i∈picks S,Share G I (untap x X i) ( untap x X (S\i))) k=tilt G T H by rw [he]; unfold Y at hv; rw [map_add] at hv; exact hv
    simp only [untap,swing,promised,Share,H, map_sum, paired, Finset.sum_apply ]; apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j _; rw [ attach (units hW h hx j.1) ( units hW h hx j.2 ), ← unfT x hi ]
end
lemma plates (h:Teams P M Q x X) (hx:∀ s k,Warm ( X s k ) false ) (s:Finset W): Response (plenum x X s) M P.η 0 := by
    let V:= team M P.η; let U:= untap x X; let T:= (spring G I).extrapolate SplitP.nat; let S:= SplitP.marked W; have he(i: Finset W): Banks (U i) 0:= fun k=> bankTilt (units hW h hx k); refine ⟨ eating he,?_⟩; have hz: U ∅=0:= by unfold U untap; rw [h.1,map_zero]
    have hp: (T.extrapolate S).valid U ((V.liftV S).move U+((2:ℂ)⁻¹) • S.Lift V.join U U):= by
        intro s; change T.valid (U s) (V.move ( U s ) + (2:ℂ)⁻¹ • (SplitP.marked W).Lift V.join U U s); rw [Stencil.halfB V.join U (fun i j=> V.rear (hedge (he i)) (hedge (he j))) hz]; exact repletes hW h hx
    exact Dynamics.expense T V S (fun i _=> hedge ( he i )) hz hp s
section
variable {s:Finset W}(h:Mesh P x)(ht:P.θ=0)(he:Teams P M Q x X)
include h
lemma epoch_s : ∃ Y, Teams P M Q x Y ∧ ∀ (s:Finset W), 2≤s.card→∀ n,Came P false (Y s n):= by
    have hm (i:W)(k:ℕ) : ∃ d:ℕ,Tip P false false d (Q i k):= by
        obtain h1:=hW i; obtain hv:= h1.1.life k; obtain ⟨b,hb⟩:=h1.2.2 k; refine ⟨ (-b).toNat,hv.heat,hv.cross,( safe_raise hb (by omega : -( ((-b).toNat):ℤ ) ≤ b ) ).highp ⟩
    exact Rake.nominal (masterD G I P) h ( fun i _=> tagD P M i ) hm
include he
lemma calls (n:ℕ)(s:Finset W): Warm ( X s n ) false:= by
    obtain ⟨Y,hV,hY⟩:= epoch_s hW h
    rcases lt_or_ge s.card 2 with hp|hp; swap; · rw [perfect he hV]; exact (hY s hp n).1.mood
    by_cases hm:s.Nonempty; swap; · rw [ Finset.not_nonempty_iff_eq_empty.mp hm,he.1]; exact CabinF.warm0
    obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from by obtain hh:= Finset.card_pos.mpr hm; omega); rw [he.2.1]; exact (hW i|>.1.life _).cross
include ht
lemma cruising : ∀ n, Known P ( X s n ) ∧ (2≤ s.card → Nilp P (X s n)) := by
    induction s using Finset.strongInductionOn with | _ s ih =>
    by_cases hh:s.card≥2; swap
    · intro n; obtain hz|hz:= s.eq_empty_or_nonempty; · rw [hz,he.1]; exact ⟨ (Nilp.zero (P:=P) (G:=G)).known, fun H=> False.elim (by simp at H)⟩ -- he dependent mismatch
      obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from by have hp:= Finset.card_pos.mpr hz; omega); rw [he.2.1]; exact ⟨ ( hW i ).2.2 n,fun hx=>False.elim (hh hx)⟩
    intro k; induction k using Nat.strong_induction_on with | h k hk=>
    have hp: Nilp P (Src x m0 K0 K0 (approach P M) X s k):= by
        refine Nilp.add (Nilp.sum _ (fun i hi=> Nilp.lonely (( hk i (Finset.mem_Ico.mp hi|>.2)).2 hh) )) ( Nilp.sum _ (fun i hi=>Nilp.sum _ (fun j hj=> ?_ )) ); exact regionA ht (Rake.space h hi) ((ih i (n_small hi|>.1 ) j.1).1) (( ih ( s\i ) (n_small hi |>.2.2.2 ) j.2 ).1)
    obtain hY:= he.2.2 s hh k; let V:=Src x m0 K0 K0 (approach P M) X s k; let Ξ:=units ( S:=s ) hW he (fun i n=>calls hW h he n i); have hw: Bank V 0:=(Bank.all_fin _ (fun i _=>( (plenary M) (k-i) ).X (Ξ i ))).add ( Bank.all_fin _ (fun i _=> Bank.all_fin _ (fun j _=> point ( units hW he (fun i n=>calls hW h he n i) _ ) ( units hW he (fun i n=>calls hW h he n i) _ ))) ); have hK:= trim_φ ( calls hW h he k s ) hw hp hY; exact ⟨ hK.2.known,fun _=>hK.2 ⟩
lemma cooldown : Stageable P (untap x X S):= fun i=> untitled ( royalU ( cruising hW h ht he i|>.1 ) ) ( RootFixed (ξ:=x) (fun i=> (hW i).2.1) )
lemma aligns (s:Finset W) : Sweep P (plenum x X s - resin x X s):= by
    let F:=untap x X; have hu(S):=cooldown ( S:= S ) hW h ht he -- order args
    refine dust_meal (P:=P) (X:=F) ?_ hu ?_
    · intro s; by_cases hP:s.card=1; · rw [Pi.sub_apply, wax,if_pos hP,sub_self]; exact Sweep.unit
      rw [ Pi.sub_apply,wax,if_neg hP,sub_zero ]; obtain hz|hz:=s.eq_empty_or_nonempty; · rw [hz,show F ∅=0 from ( by unfold F untap; rw [he.1,map_zero] ) ]; exact Sweep.unit
      exact fun k=> ( cruising hW h ht he k |>.2 ( by obtain hp:=Finset.card_pos.mpr hz; omega ) ).fixed ( RootFixed (ξ:=x) (fun i=> (hW i).2.1) )
    intro s; unfold wax; split; exact hu s; exact fun _=> Fairy.zero
end
end YM.FVA2.Extras

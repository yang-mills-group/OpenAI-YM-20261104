import YM.FVA2.LazyLoop
/-!
# Derivative of pinned branch. Translation-covariant derivative accounts for root changes

 Along a single moving source. Extend iterated. Purpose rate.
 -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.FVA2.Poesy
open YM.MS Function Set Filter Topology MeasureTheory Real Metric
open MS.Plane MS.Koszul MS.Landau Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake MS.Orbit MS.Breeze MS.Book MS.Book.Convolve Flux
open MS.Osc MS.Osc.Snap MS.City MS.Rake.Geo MS.Land MS.Local.Physical MS.Port MS.Tide MS.Vista MS.Vane MS.Dial MS.Wind MS.High MS.Fiddle Wire Belt Finset
open scoped BigOperators ContDiff Classical
variable {G: Gauge} {I W: Type} [LinearOrder W] {v:ℝ}
variable {A: Deck G}{B:Booked A}{S:MS_Data G B}
variable {x: Position W ℝ}{U V: Rake.Dance G ℝ W}{a: W→Choice v S}
variable (h:Mesh (frameF ℝ v) x)(hu:Frozen a U x) 
variable (g: W) (d:QP)
local notation "Υ"=> frameF ℝ v
local notation "Δ"=> constantP G ℝ (PlanetD G)
def awaken (g:W)(a:W→Choice v S)(d:QP): W→Choice v S:= fun i=> if g=i then derive ( a i ) d else a i
variable (hv:Frozen ( awaken g a d ) V x)
variable {Z: Set ℝ}(H:IsOpen Z)
def PathAlong (g:W)(d:QP)(x: Position W ℝ)(A:Set ℝ): Prop:=∀ i:W,∀ t∈A,HasDerivAt (x i) ( if i=g then d else 0 ) t
variable (hA:PathAlong g d x Z)
section weft
variable {w y: Finset W}
include hu hv
-- If unaffected label support there is no variation.
lemma ignores (hw: g∉w): U w=V w:= by
    induction w using Finset.strongInductionOn with| _ w ih=>
      rcases lt_or_ge w.card 2 with he|he
      · obtain hx|hx:= ( by omega: w.card=0 ∨ w.card=1 ); · rw [Finset.card_eq_zero.mp hx, hu.1,hv.1]
        obtain ⟨v',hs⟩:= Finset.card_eq_one.mp hx; rw [hs, hu.2.1, hv.2.1]; simp [ rootsRow, awaken, show g≠v' from by simpa [hs] using hw ]
      funext k; induction k using Nat.strong_induction_on with
      | h k hK=>
        obtain H:= hv.2.2 w he k; let F:= multi (fun _=> planeF) x Δ Δ ( approach Υ S ); have hM : F ( V w ) V k w=F ( U w ) U k w:= by
            unfold F multi lonely; refine congr_arg₂ (· + ·) ( Finset.sum_congr rfl (fun i hi=>?_)) ( Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j hj=>?_ ); · rw [hK i (( mem_Ico.mp hi ).2)]
            obtain ⟨a,h,b,e⟩:= n_small hi; rw [ih _ a (fun h=> hw ( a.le h )), ih _ e (fun h=>hw ( e.le h ))]
        unfold F at hM; rw [show _= _ from hM] at H 
        exact Duty.consistent ( retire _ _ ) ( hu.2.2 _ he _ ) H
omit hu hv
-- derivative of relative displacement
include hA
lemma delta (hs:w.Nonempty)(t:ℝ)(ht:t∈Z): HasDerivAt (rootX x w) (peak w d g) t := by
    have he : key w g ↔ w.min' hs=g:=⟨fun ⟨_,h⟩=>h,fun h=>⟨hs,h⟩⟩; unfold peak rootX; rw [dif_pos hs]; simpa [he] using hA (w.min' hs) _ ht
omit hA
lemma key_inc (he:key w g): g∈w:= by obtain ⟨h,rfl⟩:=he; exact min'_mem ..
-- splits.M
lemma peak_same (hy:y∈picks w): peak w d g= peak ( w \ y ) d g:= by
    let z:Position W ℝ:= fun i _=> if i=g then d else 0; have H(q:Finset W)(hq:q.Nonempty): rootX z q 0= peak q d g:=by
         unfold peak rootX; rw [dif_pos hq]; by_cases h:key q g; · rw [ if_pos h ]; obtain ⟨_,hx⟩:=h; unfold z; rw [if_pos hx]
         rw [ if_neg h ]; unfold z; exact if_neg (fun hu=> h ⟨hq,hu⟩);
    obtain ⟨i,j,f,t⟩:= n_small hy; exact ( H w ( j.mono i.le ) ).symm.trans ((congr_fun (unfT _ hy) 0 ).trans ( H _ f ))
-- packs with phase. Rewrite integral plus q root.K, not anchored at x
local notation "Ψ"=> field (Landau.parity (A:=Axis) (C:=G.ColorIndex))
section pack
variable (i j:BH G)(L R:Legs (Lane4 G))
-- use exposed Phase.IN.Exp
abbrev stable (Y:Rake.Dance G ℝ W)(x: Position W ℝ)(w y: Finset W)(g b:ℕ)(t:ℝ)(o:ℝ)(q:QP):ℂ:= bill (( rootX x y - rootX x w ) o) (q + net L) * meshZ (PlanetD G t) i j ( Y y g o t ) ( Y ( w\ y ) b o t ) L R q
lemma powered (K:Rake.Dance G ℝ W) (a b:ℕ)(i:ℝ)(t:ℝ) (l:Legs ( Lane4 G )) : regionC (fun _=>planeF) ( rootX x y-rootX x w ) Δ ( K y a ) ( K ( w\ y ) b ) i t l=scatter Ψ l (fun L R=> ∑ j:BH G,∑ k:BH G,∫ u,stable j k L R K x w y a b t i u∂planeF):= by
     unfold regionC Cabin; refine scatter_congr _ _ _ _ (fun L R hp=>?_); rw [Finset.mul_sum ]; apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum ]; apply Finset.sum_congr rfl; intro k _; rw [ ← integral_const_mul ]; refine integral_congr_ae ( Eventually.of_forall (fun i=>?_)); unfold stable; rw [ rightadd ]; ring_nf
variable {i j L R}
include h hu
lemma fuelM (hy:y∈picks w) (a b:ℕ)(t:ℝ): Sec (stable i j L R U x w y a b t ) planeF := by
    obtain ⟨e,z,v,c⟩:= n_small hy; exact Sec.tempo (fun i q=> bill _ _) (fun i=> (sailor _).shore.comp (continuous_id.add continuous_const)) ( fun i q => bill_norm ..|>.le ) ( packP h hu t z v a b L R ) -- goal
omit h
omit hu
lemma strike_sym (d s:QP) : strike d s=strike s d:= by simp only [strike_beam,Momentum.pairing,mul_comm]
lemma strike_zero (d:QP) : strike 0 d=0:= by rw [strike_sym, map_zero]
include hu hv hA
variable {g d} {l:Legs (Lane4 G)}
lemma central (hy:y∈picks w)(t q:ℕ)(he:grade Z d g y (U y t) (V y t)) (h':grade Z d g ( w\y ) ( U (w\y) q ) (V (w\y) q))(r:ℝ)(s:QP)(hp:Split L R l): direct Z ( liftP w g ) ( strike ( peak w d g ) ( net l ) ) (fun o=>stable i j L R U x w y t q r o s) (fun o=>stable i j L R V x w y t q r o s):= by
    intro x hx; obtain ⟨T,f,vY,k⟩:= n_small hy; let A:= (i,s)::L; let B:= ( j,-s)::R;
    have h2:= delta g d hA (f.mono T.le) x hx; have hl:=delta g d hA f x hx; let c:ℂ:= cross ( parity j ) ( degree Ψ L ); have ha:= he A r x hx; have hb:= h' B r x hx; have hh:= drives (hl.sub h2) (s+net L); let y':= w\ y;
    unfold stable meshZ; apply HasDerivAt.congr_deriv ( hh.mul (( (ha.const_mul c).const_mul (2* ( PlanetD G r ) i j s) ).mul hb ) ); -- mismatches order.cons
    have hw:= peak_same g d hy; let p:= peak w d g; let V':= peak y d g; let o:= net l;
    dsimp only at *; rw [ net_cons, net_cons, ← hw ]; simp_rw [ ← split_net hp, strike_sym (peak y d g- _),map_sub ]; simp_rw [ strike_sym (s+net L) ]; -- cancel
    by_cases hg:g∈y
    · have H:= ignores hu g d hv ( w:= w \ y ) ( fun e=> (Finset.mem_sdiff.mp e).2 hg ); -- order args
      dsimp only [A,B,c]; simp_rw [ liftP ]; rw [ if_pos hg,if_neg (fun he=> ( Finset.mem_sdiff.mp he ).2 hg),if_pos (T.le hg),H ]; simp only [Pi.mul_apply,map_add,map_neg]; ring
    dsimp only [A,B,c]; rw [ ignores hu g d hv hg, show liftP y g=0 from if_neg hg, show liftP ( w\y ) g= liftP w g from (by unfold liftP; simp [hg]) ]; simp only [Pi.mul_apply,map_add,map_neg]; ring
end pack
end weft
end YM.FVA2.Poesy

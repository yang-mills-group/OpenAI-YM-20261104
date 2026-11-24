import YM.FVA2.O.Fusion.Filled
/-!
# Rephase the mark kernels & calculate the connected equation

`rookie`: from `DOrd`, connected evolution with the same `helm` as
for a singleton, and the cross terms `Share`. Works even for noncompact
layouts under the stated `Warm` hypotheses (see `Pantry/Main`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Fuse
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff Serve Rake.Geo Vane
open scoped Topology ContDiff Interval
variable {G:Gauge} {I E W:Type}[LinearOrder W]{L:Planet G I}{B: Deck G}{K:Booked B}{M:MS_Data G K}{q:ℤ}{P:Geo I}{x:Position W I} {p a b:I→QP}{R:W→Rake.Label B}{X:Rake.Dance G I W}{S:Finset W}
local notation "Λ0"=> (fun _ : I=> lineA G)
local notation "m0"=> (fun _:I=> planeF)
abbrev untap (x:Position W I)(X:Rake.Dance G I W)(s:Finset W):= swing G (rootX x s) ( X s )
omit [LinearOrder W] in
lemma hel_core {η:I→ℝ}{Y:T (Glade G I)}(n:ℕ): helm M η Y n=(both G I).P (Y n)+ lonely Λ0 (gather M η) Y n:= by
    let X:= gather M η; change _+pairW (both G I).X (gather M η) Y n=_; rw [paired,Tone.Frame.canon_sub (fun i j=>(both G I).X ((gather M η) i) (Y j)), zero_B M,map_zero,LinearMap.zero_apply,zero_add ]; rfl -- X let?
omit [LinearOrder W] in
lemma hel_core' {η:I→ℝ}{Y:T (Glade G I)}(n:ℕ)(hp:Banks Y q): helm M η Y n=sailP m0 Λ0 (Y n)+ lonely Λ0 (gather M η) Y n:= by rw [hel_core, show (both G I).P (Y n)= _ from spine (hp n|>.cross) realityA ]
variable (h:DOrd K P M R x X)(hx:∀ s k,Warm (X s k) false)
include h hx
lemma rookie : ∀ n, Velocity ( untap x X S n ) ((helm M P.η (untap x X S) +∑ i∈ picks S, Share G I (untap x X i) (untap x X ( S\ i ))) n) := by
    by_cases he:S.card<2
    · obtain hs|⟨i,rfl⟩:= ( by by_cases hv:S=∅; exact Or.inl hv; exact Or.inr ( Finset.card_eq_one.mp (by have h:0< S.card:= Finset.card_pos.mpr ( Finset.nonempty_iff_ne_empty.mpr hv ); omega) ) : S=∅ ∨ ∃ i:W,S={i} )
      · subst S; rw [show picks (∅:Finset W)=∅ from ( by ext; simp [ picks ] ), show untap x X ∅=0 from ( by unfold untap; rw [h.1,map_zero] ) ]; simp only [map_zero, Finset.sum_empty, add_zero]; exact fun _ _ _ _=> hasDerivAt_const ..
      · rw [show picks ({i}: Finset W)=∅ from Finset.eq_empty_iff_forall_notMem.mpr fun k hk=> clips (by simp) hk,Finset.sum_empty,add_zero]; unfold untap; rw [h.2.1]; exact (snakeV (p:=rootX x {i}) (Response.visit (M:=M) (η:=P.η) ( ( R i ).item ))).vital
    have hm:= solitude h hx ( S:=S ); intro k; obtain ⟨h₁,h₂,h₃⟩:= h.2.2 S (le_of_not_gt he) k; let F:=gather M P.η; let H:=∑ i∈ picks S,∑ j∈ antidiagonal k, regionC m0 (rootX x i-rootX x S) Λ0 (X i j.1) ( X (S\i) j.2 ); let Y:= helm M P.η (X S) k+H; let T:= rootX x S; obtain hY : sailP m0 Λ0 (X S k)+ multi m0 x Λ0 Λ0 F (X S) X k S= Y:= Eq.trans (Eq.symm (add_assoc _ _ _)) (congr_arg (· + H) ( hel_core' k hm ).symm); change X S k=river ( sailP m0 Λ0 ( X S k )+multi m0 x Λ0 Λ0 F (X S) X k S ) at h₃; rw [hY] at h₃; change Job.train false ( sailP m0 Λ0 ( X S k ) +multi m0 x Λ0 Λ0 F (X S) X k S ) at h₂; rw [hY] at h₂
    have hh : Bank H 0:= Bank.all_fin _ (fun i hi=> Bank.all_fin _ (fun j hj=> point ( solitude h hx _ ) ( solitude h hx _ )))
    have he':Bank Y 0:= ( (( plenary M ).lives hm) k ).add hh
    have hW : Velocity (X S k) Y:= by rw [h₃]; intro i t w; rw [funext (fun t=> swamp h₂ i t 0 (v:=w) (fun x=>Bool.noConfusion x))]; exact ( hfun ( he'.cross.walk _ _ (fun x=>Bool.noConfusion x) ) t).const_add _
    have hv:= velTilt (p:=T) hW; change Velocity _ ((helm M P.η (swing G T (X S))+ _) k); rw [ ← helion (hx S), Pi.add_apply ]; suffices he : (∑ i∈picks S,Share G I (untap x X i) ( untap x X (S\i))) k=tilt G T H by rw [he]; unfold Y at hv; rw [map_add] at hv; exact hv
    simp only [untap,swing,promised,Share,H, map_sum, paired, Finset.sum_apply ]; apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j _; rw [ attach (solitude h hx j.1) ( solitude h hx j.2 ), ← unfT x hi ]
end YM.FVA2.O.Fuse

import YM.FVA2.Extras.Principal
/-! # Promoting single-order decomposition to simultaneous in perturbative order

Auxiliary to `YM/FVA2/Extras/Result.lean`. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
variable {I:Type}{G:Gauge}{B:Deck G}{K:Booked B}{M:MS_Data G K}{F:Glade G Unit}
variable {b d:ℤ}{r k n:ℕ}{u t:ℝ}{X Y:T ( Glade G Unit )}
open O.Hue
-- decompose one rank. select fixed k-order slope
variable {h:ℕ}{V:T (localX G)}{P:Package B h}
lemma calm_flux (p:Package B h)(h0:Quiet X n) (F:T (localX G)): Quiet ( X-plot u M p F n ) n:= by
    intro i hi; rw [ Pi.sub_apply, h0 i hi,plot,low_hold hi,sub_zero ]
lemma trim (hm:Diversity ( X n ) k) (he:Narrow X n k t=0): ∀ l: Legs (Lane4 G), (k:ℤ)-1<l.length→ X n () t l=0:= by
    intro l hl; by_cases hx:l.length=k; rw [← enough (F:=X n () t) l ( by omega : (l.length:ℤ)=(k:ℤ) ) ]; exact congr_fun he l; exact hm () t l (by omega)
lemma First.next (H:First X u h n k)(hp:Forth u M X h): ∃ (p:Package B h) (V:T (localX G)), ghostly u M V (h-1) ∧ Diversity ((X-plot u M p V n) n) ((k:ℤ)-1):= by
    obtain ⟨p,V,hv,hC,hE⟩:= Principal.eligible (M:=M) (u:=u) (n:=n) (Narrow X n k 0) ( H.form hp.1.1 ) ( H.sees hp.1 ); let W:=X-plot u M p V n; obtain hQ:= hp.subtract (plotted (n:=n) p hv); have hx : First W u h n k:=⟨ calm_flux p H.calm _,hQ.2 n,fun i t=>(H.limit i t).sub (hC i t)⟩; have h0: Narrow W n k 0=0:= by simp only [Narrow] at hE ⊢; simp only [W,Pi.sub_apply,map_sub,hE,sub_self];
    refine ⟨p,V,hv,fun i t=>?_⟩; exact trim hx.limit (( hx.flat hQ.1.1 ).trans h0)
lemma First.all (H:First X u h n k)(hp:Forth u M X h): ∃ (p:Package B h) (V:T (localX G)), ghostly u M V (h-1) ∧ (X-plot u M p V n) n=0:= by
    induction k generalizing X with
    | zero=> obtain ⟨p,V,hp,hV⟩ := H.next hp; exact ⟨p,V,hp,funext (fun i=>funext fun t=>funext fun l=> hV i t l (by omega))⟩
    | succ k ih=> obtain ⟨p,V,hQ,hV⟩ := H.next hp; have ht:= hp.subtract (plotted (n:=n) p hQ); obtain ⟨q,Y,hY,h⟩:= ih ⟨ calm_flux p H.calm _,ht.2 n,(by simpa using hV)⟩ ht; exact ⟨ p+q,V+Y, ⟨ hQ.1.add hY.1,hQ.2.plus hY.2 ⟩,(by rw [plots, ← sub_sub,h])⟩
lemma rapid (H: Quiet X n)(hX: Forth u M X h): ∃ (p:Package B h) (Y:T (localX G)), ghostly u M Y (h-1) ∧ Quiet ( X - plot u M p Y n ) (n+1) := by
    obtain ⟨k,hk⟩:= hX.1.1.life n|>.heat; obtain ⟨p,Y,hY,h'⟩:= First.all ⟨ H,hX.2 n,hk ⟩ hX; exact ⟨ p,Y,hY,(fun i hi=> if he:i=n then he.symm ▸ h' else calm_flux p H Y i (by omega)) ⟩
-- sums locally finite and choices independent of order
structure Scratch (u:ℝ)(M:MS_Data G K)(h n:ℕ) where
    residual : T (localX G)
    valueB : Package B h
    valueV : T (localX G)
    even : Forth u M residual h
    errand : Quiet residual n
    right : ghostly u M valueV (h-1)
    next : Quiet (residual-plot u M valueB valueV n) (n+1)
def Grind (X:T (localX G))(n:ℕ)(hp:Quiet X n)(hX:Forth u M X h): Scratch u M h n where
    residual:= X
    valueB:= Classical.choose ( rapid hp hX )
    valueV:= Classical.choose ( Classical.choose_spec ( rapid hp hX ) )
    even:= hX
    errand:=hp
    right:= (Classical.choose_spec (Classical.choose_spec ( rapid hp hX ) )).1
    next:= (Classical.choose_spec (Classical.choose_spec ( rapid hp hX ) )).2
abbrev Scratch.after_q (S: Scratch u M h n):= S.residual - plot u M S.valueB S.valueV n
def track (X:T (localX G)) (u:ℝ)(hX:Forth u M X h) : ∀ n:ℕ, Scratch u M h n
| 0=> Grind X 0 (fun _ h=>by omega) hX
| n+1=> let P:= track X u hX n; Grind P.after_q (n+1) P.next ( P.even.subtract ( plotted P.valueB P.right ) )
lemma ahead (V:Forth u M X h)(k:ℕ): (track X u V k).residual=X-∑ i ∈ Finset.range k,plot u M (track X u V i).valueB (track X u V i).valueV i:= by
    induction k with
    | zero=> change X=_; simp
    | succ k ih=> rw [ show (track X u V (k+1)).residual=(track X u V k).after_q from rfl, Finset.sum_range_succ, ← sub_sub,← ih]
lemma quarry (V:Forth u M X h): ∃ (p:T (Package B h))(Y:ℕ→ T (localX G)),(∀ i, ghostly u M (Y i) (h-1) ) ∧ ∀ n:ℕ,Quiet ( X-∑ i ∈ Finset.range n,plot u M ( p i ) ( Y i ) i ) n:= by
    exact ⟨ _,_,fun i=> (track X u V i).right,( fun i=> ahead V i ▸ (track X u V i).errand )⟩
end YM.FVA2.Extras

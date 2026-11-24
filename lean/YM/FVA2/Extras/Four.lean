import YM.FVA2.Extras.Residue
/-! # Actual projection: decompose `Forth` into an all-orders physical
combination and exact term in the specialized system (`cleanMultiple`)

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
open MS.Garment MS.Garment.Wick MS.Garment.Wave MS.Land MS.Rake.Geo MS.Hem MS.Hem.Mell MS.Motif Literal Dock MS.Arts -- remove
variable {h:ℕ}{Y:Blue G}{V: T (localX G)}{U:T (Arts.Mob G)}{Q:CostsM G}
lemma whr (he:comet h 0 M.bulk ( gloss U ) Y Q)(hm:Trill (pulseX G) U) : let S:= peek ( letIn h (logMass u) Y ) () t; (Φ G t).res (Pulse M u t) S=0 := by
    intro S; let P:= Pulse M u t; let X:= B0 G t 0; ext n l; have hp : (Wick.Q G 0).raise (S n) l= High.Ward id (High.spaceD G) n 0 1 (Archive 4 M.bulk) (Archive h Y) (u,t) l:= (Outlook.fieldD M.bulkOK he wisdom hm).master.qfm n _ _ (by omega) (fun x=>Bool.noConfusion x) (fun x=>Bool.noConfusion x); unfold High.Ward at hp
    rw [ trunkM ( y:=u ) ( s:=t ) (U:=X) (High.degreeMaster id (High.spaceD G)) (center M) rfl rfl (rB.pays Geo.Coherent (fullW (Host.host (gang (he n))))) ] at hp; change (((Wick.Q G 0).raise (S n)+orbit X planeF (S n))+pairW (boulevard Landau.parity X) P S n) l=0; simp only [add_assoc,Pi.add_apply,hp]; exact neg_add_cancel _
lemma appears (he:comet h 0 M.bulk ( gloss U ) Y Q)(hm:Trill (pulseX G) U): Forth u M ( letIn h (logMass u) Y ) h:= by
    refine ⟨ ⟨ Response.mark he,funext fun n=> funext fun i=> funext fun t=> ?_ ⟩,cometClean he ⟩; change peek _ () t n=0; rw [steers M,show logMass u ()=u from rfl]; exact congr_fun ( whr he hm ) n
-- Honest series combination, consolidate.
abbrev many (u:ℝ)(M:MS_Data G K)(p:T (Package B h)) : T (localX G):= ∑ i, entrance (fun n (_:Unit)=> p n i) ( soloV _ ( logMass u ) M i )
variable {p:T (Package B h)}{Z:T (T (localX G))}
lemma batch (hk:k≤ n): many u M p k=( ∑ i∈Finset.range (n+1), hold0 i (chosen u M (p i))) k:= by
    simp_rw [many, Finset.sum_apply, ← hereΛ ( A:=fun i (_:Unit)=>p i _ ) hk,hall,Finset.sum_apply]; rw [ Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; by_cases he:i≤ k; swap; · simp_rw [low_hold ( n:=i ) ( k:=k ) (Nat.lt_of_not_ge he), Finset.sum_const_zero]
    simp_rw [hx_holder he,chosen,Finset.sum_apply]
abbrev fully (Z:T (T (localX G))) : T (localX G):= fun n=> ( ∑ i∈ Finset.range (n+1),hold0 i (Z i) ) n
abbrev brief (Z:T (T (localX G)))(n:ℕ):= ∑ i∈ Finset.range (n+1),hold0 i (Z i)
lemma brief_c : sameΛ n ( brief Z n ) ( fully Z ):= by
    intro i hi; unfold brief fully; simp_rw [Finset.sum_apply]; exact Eq.symm ( Finset.sum_subset ( Finset.range_mono ( by omega ) ) (fun j hj h'=> low_hold ( by simp only [ Finset.mem_range ] at h'; omega )) )
lemma full_response (h:∀ i,ghostly u M (Z i) d): ghostly u M (fully Z) d:= by
    have H(n:ℕ): ghostly u M ( brief Z n ) d:=⟨ Response.all_fin _ (fun i _=> shift_Response ( h i ).1 ), honest_S _ fun i _=> (h i).2.raise _ ⟩; refine ⟨⟨ fun i=> ?_,fun n=>?_⟩,(fun i=> ( H i ).2 i )⟩; · exact (H i).1.life i
    rw [helm, ← commuteΛ ( G:=G ) ( both G Unit ).X ( both G Unit ).P (Lives.gather M (logMass u)) brief_c (i:=n) (le_refl n) ]; exact (H n).1.vital n
lemma cleanMultiple (V:Forth u M X h): ∃ (p:T (Package B h))(Y:T (localX G)), ghostly u M Y (h-1) ∧ X=many u M p + nav M (logMass u) Y := by
    obtain ⟨p,Y,hY,h⟩:=quarry V; refine ⟨ p,fully Y,full_response hY,?_ ⟩; funext n; obtain hp: X n= (∑ i∈Finset.range (n+1), plot u M (p i) (Y i) i) n:= sub_eq_zero.mp (h (n+1) n (Nat.lt_succ_self n));
    rw [hp,Pi.add_apply, batch (le_refl n),nav,← commuteΛ ( both G Unit ).C ( both G Unit ).J ( Lives.gather M (logMass u) ) brief_c (i:=n) (le_refl n) ];
    change (∑ i∈ Finset.range (n+1), plot u M (p i) (Y i) i) n = _+ ( nav M (logMass u) ( brief Y n ) ) n; unfold brief plot; simp_rw [map_sum,Finset.sum_apply, shift_R,hold_add,Pi.add_apply, Finset.sum_add_distrib ]
-- actual `MS_Data` convention. not using off-shell tensor choices not present in target.
theorem realizes (he:Trill (pulseX G) U)(hV:Schema false 0 h ( gloss U )): ∃ Y Q, comet h 0 M.bulk ( gloss U ) Y Q ∧ ∀ u:ℝ, ∃ (p:T (Package B h))(X:T (localX G)),ghostly u M X (h-1) ∧ letIn h (logMass u) Y=many u M p+nav M (logMass u) X:= by
    obtain ⟨Y,Q,hY⟩:= satisfyY M.bulkOK hV; exact ⟨Y,Q,hY,(fun _=> cleanMultiple (appears hY he)) ⟩
lemma gallery_field {V:Literal.Box ( Arts.Mob G )}{L:Law G} (he: Mach.Ele h k L V) : ∃ Y Q, comet h 0 M.bulk ( gloss ( Literal.linear (Arts.Mob G) V )) Y Q ∧ ∀ u:ℝ, ∃ (p:T (Package B h))(X:T (localX G)), ghostly u M X (h-1) ∧ letIn h (logMass u) Y=many u M p+nav M (logMass u) X:= realizes he.moodQ he.grows
end YM.FVA2.Extras

import YM.FVA2.Extras.Mask
/-! # Eligible at leading: matching the free closed condition and obtaining `Principal`

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
-- fixed independent representatives.News from `quarry`. Final proofs further on
variable {h:ℕ}{l:Law G}
open O.Hue
abbrev Forth (u:ℝ)(M:MS_Data G K)(X:T (localX G))(h:ℤ): Prop:= Certified X M (logMass u) 0 ∧ Honest u X h
abbrev ghostly (u:ℝ)(M:MS_Data G K)(X:T (localX G))(h:ℤ): Prop:= Response X M (logMass u) (-1) ∧ Honest u X h
lemma Forth.subtract (H:Forth u M X d)(h:Forth u M Y d): Forth u M (X-Y) d:= ⟨C_sub H.1 h.1,H.2.sub h.2⟩
lemma q_approved (h:ghostly u M X (d-1)): Forth u M (nav M (logMass u) X) d:= ⟨ by simpa only [ neg_add_cancel ] using h.1.ward, (sub_add_cancel d 1) ▸ Honest.nav h.2 h.1⟩
abbrev Package (B:Deck G)(h:ℕ):= (Land.Plaid B h)→ℝ
abbrev chosen (u:ℝ)(M:MS_Data G K)(p:Package B k): T (localX G):= ∑ i, seat (fun _=>p i) (soloV _ (logMass u) M i)
lemma choice_A (p:Package B k)(q:Package B k): chosen u M (p+q)=chosen u M p+chosen u M q:= by
    simp_rw [ chosen, show ∀ i, (fun _:Unit=>(p+q) i)=(fun _=>p i)+(fun _=> q i) from fun _=>rfl,orientR, Finset.sum_add_distrib]
@[simp] lemma choice₀ : chosen u M (0:Package B k)=0:= by
    unfold chosen; apply Finset.sum_eq_zero; exact fun i _=>seat0 _
lemma choiceᵢ (i:Land.Plaid B k)(a:ℝ): chosen u M ( (Pi.single i a):Package B k )= seat (fun _=>a) ( soloV _ (logMass u) M i):= by
    unfold chosen; rw [ Finset.sum_eq_single i, Pi.single_eq_same]; intro j _ he; rw [ Pi.single_eq_of_ne he ]; exact seat0 _; simp
lemma honest_S (s:Finset I){f:I→ T ( localX G )}(h:∀ i∈s,Honest u (f i) d): Honest u (∑ i∈s,f i) d:= by classical induction s using Finset.induction_on with| empty=> rw [ Finset.sum_empty ]; exact Honest.zero| insert i s hi ih=> rw [ Finset.sum_insert hi ]; exact (h i (by simp)).plus ( ih fun j hj=> h j (mem_insert_of_mem hj))
lemma basis_q (p:Package B k): Forth u M (chosen u M p) k := ⟨ C_ο _ (fun i _=> C_seat ( Certified.first i ) ), honest_S _ fun i _=> ( cometClean ( M.markOK k i ) ).cost (p i) ⟩
-- constant power shift plus exact choice from step
abbrev plot (u:ℝ)(M:MS_Data G K)(p:Package B h)(Y:T (localX G))(n:ℕ): T (localX G):= hold0 n ( chosen u M p + nav M (logMass u) Y )
lemma plots (p q:Package B h): plot u M (p+q) (X+Y) n= plot u M p X n+ plot u M q Y n:= by unfold plot; rw [map_add,choice_A,show chosen u M p+chosen u M q+(_+_)=_ from (show _=chosen u M p+nav M (logMass u) X+(chosen u M q+nav M (logMass u) Y) from by abel) ,hold_add]
lemma plotted (p:Package B h)(he:ghostly u M Y (h-1)): Forth u M (plot u M p Y n) h:= by
    -- coercion: `h` nat yes
    obtain h0:=q_approved he; obtain ht:= basis_q (u:=u) (M:=M) p; exact ⟨ shift_C (C_add ht.1 h0.1), Honest.raise ( ht.2.plus h0.2 ) _ ⟩
@[simp] lemma plot₀ : plot u M (0:Package B h) 0 n=0:= by rw [plot,choice₀,map_zero,add_zero,holdZ]
def Principal (u:ℝ)(M:MS_Data G K)(h k n:ℕ)(F:Law G) : Prop:= ∃ (p:Package B h) (Y:T (localX G)), ghostly u M Y (h-1) ∧ Diversity (plot u M p Y n n) k ∧ Narrow (plot u M p Y n) n k 0=F
namespace Principal
variable {v w:Law G}
lemma plus (H:Principal u M h k n v)(hp:Principal u M h k n w): Principal u M h k n (v+w):= by
    obtain ⟨p,Y,hP,h,R⟩:=H; obtain ⟨q,Z,hQ,hz,T⟩:=hp; refine ⟨ p+q,Y+Z, ⟨ hP.1.add hQ.1,hP.2.plus hQ.2⟩,?_,?_⟩;
    · rw [ show plot u M (p+q) _ n= _ from plots .. ]; exact uh h hz
    rw [ show plot u M (p+q) _ n=_ from plots .. ]; unfold Narrow; simp only [ Pi.add_apply,map_add ]; rw [← R,← T]
lemma zero : Principal u M h k n 0 := ⟨0,0,⟨ Response.zero,Honest.zero⟩,(by rw [plot₀]; exact fun _ _ _ _=>rfl),(by rw [ plot₀ ]; exact map_zero _ ) ⟩
lemma sum (s:Finset I){F:I→Law G}(hp:∀ i∈s,Principal u M h k n (F i)): Principal u M h k n (∑ i∈s,F i):= by classical induction s using Finset.induction_on with| empty=>rw [Finset.sum_empty]; exact zero| insert i s hi ih=> rw [ Finset.sum_insert hi ]; exact ( hp i (by simp) ).plus ( ih fun j hj=>hp j (mem_insert_of_mem hj) )
lemma from_basis (p:Plaid B h)(a:ℝ): Principal u M h p.1.val n (a • (Land.read p).read ):= by
    obtain hp:= Mach.initialHF ( K.law _ p ) ( Land.sizeG p ) (M.markOK _ p);
    refine ⟨ Pi.single p a,0,⟨ Response.zero,Honest.zero⟩,?_,?_⟩ <;> simp only [plot, Narrow, choiceᵢ, map_zero, add_zero,hold_1] -- check
    · exact fun i t=> ( hp.too (logMass u i,t) ).smul (a:ℂ)
    rw [show seat _ _ 0 () 0= _ from ( show _=(a:ℂ) • ((Outlook.Archive h ( M.marks h p ) 0 (u,0)):Law G) from rfl ),map_smul]; exact congr_arg ((a:ℂ) • · ) ( hp.top (u,0) )
lemma from_extra (he:l∈ Local.Physical.Lease G ((h:ℤ)-1) k (-1)): Principal u M h k n ( natQ l ):= by
    cases h with
    | zero => rw [show l=0 from ?_,natQ,map_zero]; exact zero; funext s; exact ( lease_one.mp he ).2.1.no_tall s (fun x=>Bool.noConfusion x) (by have hh:= length_pay s; omega)
    | succ h=>
       have H:l ∈ Local.Physical.Lease G h k (-1):= by simpa using he
       obtain ⟨Y,Q,hY⟩:= gift M H; let X':=letIn h ( logMass u ) Y; obtain hp : Response X' M (logMass u) (-1):= Response.mark hY; obtain hV:= ward_z hp ( yarn H Y Q hY ) ( lease_one.mp H ).2.2; refine ⟨ 0,X',⟨ hp,( by convert cometClean (u:=u) hY using 1; first|rfl| omega ) ⟩,?_,?_⟩ <;> simp only [plot, Narrow,choice₀,zero_add,hold_1];
       · exact hV.reach
       ext l; by_cases he:l.length=k; rw [enough _ (by omega),hV.tops () 0 l he]; exact (strange _ (by omega)).trans ( rankQ ( lease_one.mp H ).2.2 l (fun x=>Bool.noConfusion x) he ).symm
lemma eligible (F:Law G)(he:F∈Local.Physical.Lease G h k 0)(hc:natQ F=0): Principal u M h k n F := by
    obtain ⟨p,L,hP,hL⟩ := B.combine he hc
    have ht(i:B.BIndex h k): k ≤ h := by
        by_contra! H; have h':=B.ceiling (h:=(h:ℤ)) (r:=k) (by omega); have hv:=i.isLt; have hz : Module.finrank ℝ (B.carries (↑h) k)=0:= by rw [ h',finrank_bot ]
        omega
    rw [← hL]; exact ( Principal.sum _ (fun i _=> from_basis ( ⟨⟨k,Nat.lt_succ_of_le (ht i)⟩,i⟩: Plaid B h ) (p i) ) ).plus ( Principal.from_extra hP ) -- infer trouble
end Principal
end YM.FVA2.Extras

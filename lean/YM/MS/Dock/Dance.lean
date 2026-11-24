import YM.MS.Dock.Assembly
/-!
# Practical F-label packages

Nonlinear tree starts from caffeine scale. `Badge` is exactly requirements for classical entry (except independence of ζ & R, closability etc). Include $Γ$.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dock
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I A:Type}{G:Gauge}{X Y F J:Flats G}{b c:Bool}{t v r:ℤ}{n m h ℓ:ℕ}{i:ℂ}{f g p:Coat G}{D:Prop}
structure Badge (b:Bool)(f:Coat G) (h:ℕ)(t:ℤ): Prop where
   born:Count f h
   stock:∃ r,Cap0 b t r f
structure Gang (b:Bool)(h:ℕ)(i:ℤ)(X: Flats G): Prop where
   price:∃ r, ClockD b i r X
   dost: Stay h X
   tail:∃ f,Return X f h
lemma gang (hp:sings b t h f D J X p): Gang b h t X:= by obtain ⟨⟨r,hT,Q,X⟩,H⟩:=hp; exact ⟨⟨_,Q⟩,hT.toll,⟨_,hT.sip⟩⟩
abbrev drive0 (G:Gauge):= TreeN (A0 G 0)
lemma feed (hX:Gang b 4 t X)(hH:Gang b n v F): ∃ r, Coal b n (t+v) r (drive0 G X F):= by
    obtain ⟨⟨r,H⟩,hp,p0,hP⟩:=hX; obtain ⟨⟨s,hF⟩,ht,S,hS⟩:=hH
    exact ⟨ r+s-2, fun i=>⟨ blazeB (F:=X) (X:=F) (fun i=>(H i).fine) (fun i=>( hF i).fine) i, capA (clockCap H) (clockCap hF) (reverse_a G 0) i⟩, StayB (U:=A0 G 0) (b:=b) (a:=4) (by push_cast; ring) (c_bo 0) (reverse_a G 0) hp ht,sip_pp hP hS⟩ -- $Γ`
lemma gangLo (hp:Gang true h t X) : Gang b h t X:= by cases b; obtain ⟨⟨r,hR⟩,hT,H⟩:= hp; exact ⟨⟨r,fun i=> ⟨(hR i).fine.tire, (hR i).cap⟩⟩,hT,H⟩; exact hp
lemma Coal.wax (h: Coal b n t r X)(he:r≤v): Coal b n t v X:= ⟨ clockTrans h.eye he,h.real,h.force⟩
lemma coal_zero (b:Bool)(n:ℕ)(t r:ℤ): Coal b n t r (0:Flats G):= ⟨ fun i=> Cap0.zero,(Joint.zero (n:=n)).toll,by simpa only [add_zero] using (Joint.zero (G:=G) (n:=n)).sip⟩
lemma glow (hp: Coal b n t r X)(hL: Coal b n t r F) : Coal b n t r (X+F):= ⟨ Cap0.heap.plus hp.eye hL.eye,Stay_add hp.real hL.real, by simpa only [add_zero] using sip_plus hp.force hL.force ⟩
lemma glow_sum {F:I→ Flats G}(S:Finset I)(hx:∀ i∈S,∃ r,Coal b n t r (F i)) : ∃ r, Coal b n t r (∑ i∈S,F i) := by
   classical
   induction S using Finset.induction with
   | empty=> rw [Finset.sum_empty]; exact ⟨0,coal_zero ..⟩
   | insert j s hj ih=>
       obtain ⟨r,hp⟩:= hx j (by simp); obtain ⟨q,hq⟩:= ih fun i hi=> hx i (Finset.mem_insert_of_mem hi); rw [Finset.sum_insert hj]; exact ⟨ _, glow (hp.wax (le_max_left r q)) ( hq.wax (le_max_right r q))⟩
lemma glazer (h:Coal b n t r J)(k:ℂ)(hk:star k=k): Coal b n t r (k • J):= ⟨ fun i=> (h.eye i).smul hk, Stay_scale h.real k, by simpa only [smul_zero] using sip_static k h.force⟩
lemma vocals (hT:¬D)(h:Badge b f n t)(hp:∃ r,Coal b n t r J): ∃ X p, sings b t n f D J X p:= by obtain ⟨r,hx⟩:=hp; obtain ⟨v,hv⟩:=h.stock; obtain ⟨X,p,H⟩:= factory (hx.wax (le_max_left r v)) h.born (hv.collects (le_max_right r v)); exact ⟨X,p, ⟨_, H⟩,fun x=> (hT x).elim⟩
lemma zero_sing (D:Prop): sings b t n (0:Coat G) D 0 0 0:= by refine ⟨⟨0,?_,fun _=>Cap0.zero,Cap0.zero⟩,fun _=> rfl⟩; rw [map_zero,add_zero]; exact Joint.zero
lemma pact_scaled (h:Pact X Y)(c:ℂ): Pact (c•X) (c•Y):= fun i=> (h i).mono (fun _ hi=> congr_arg (c • ·) hi)
lemma pact_sum (J:Finset I){X Y:I→ Flats G}(hp:∀ i∈J,Pact (X i) (Y i)): Pact (∑ i∈J,X i) (∑ i∈J,Y i):= by
   classical
   induction J using Finset.induction with| empty=> rw [Finset.sum_empty,Finset.sum_empty]; intro i; rfl| insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact common (hp i (by simp)) (ih fun j hj=> hp j (Finset.mem_insert_of_mem hj))
end YM.MS.Dock

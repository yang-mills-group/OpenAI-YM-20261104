import YM.MSbar.Grid.Deck

/-! Compact supports on hitting operations only, Fourier sector sampling with both momentum words. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Loops
open Function Finsupp Super Finset Filter Set MeasureTheory
open scoped BigOperators Classical Topology
variable {C M:Type*} [AddCommGroup M] [MeasurableSpace M] [TopologicalSpace M] {μ:Measure M} {B:Snap M μ} {I:Finset C} (S:Line C M)
variable {F G: ℕ→ Amps C M}{f g:Amps C M}{k : Bit}{p : C→Bit}
structure Supported (S:Line C M)(I:Finset C): Prop where
   light (a b : C): a∈I→ b∈I→Continuous (S a b)
   rises : ∃ K : Set M,IsCompact K ∧ ∀ a∈ I,∀ b∈ I, Function.support (S a b)⊆ K
-- all low derivatives out of `P` have common compact support; no continuity features on n-period approxim
variable {S}
private lemma follows (b:ℕ→ℕ)(hb : Tendsto b atTop atTop)(x:Ticket B.clan b) (hs:Supported S I)(a c:C)(ha:a∈I)(hc:c∈I):
    Tendsto (fun n=> held (B.layer (b n)) S a c (x.f n)) atTop (𝓝 (S a c x.target)):=by
    obtain ⟨J,hJ,H⟩:=hs.rises
    refine (((hs.light a c ha hc).tendsto x.target).comp x.tend).congr' ?_
    filter_upwards [hb.eventually (B.eventually _ hJ)] with i hi
    unfold held comp; split_ifs with h; rfl
    exact not_not.mp (fun hN=> h (hi ⟨H _ ha _ hc hN,x.belongs i⟩))
variable [IsTopologicalAddGroup M]
namespace Copies
lemma tree (hf:Copies B.clan F f)(hg:Copies B.clan G g)(hs:Supported S I)(p:C→Bit) (d:Bit): Copies B.clan (fun i=> pairs (lift p) d (Stocking I (B.layer i) S) (F i) (G i)) (Loops.tree p I d S f g):=by
   refine ⟨fun n=> by rw [moment_pair _ (hf.clear n)]; exact hg.clear n|>.tree,hg.quiet.tree,?_⟩
   intro w hw u hu; simp_rw [moment_pair _ (hf.clear _),Loops.tree]
   refine tendsto_finsetSum _ fun a ha=> tendsto_finsetSum _ fun b hb=> ?_
   have he(n):= splitting (lift p) (lift p) (fun x:C × Ticket B.clan w=>(x.1,x.2.f n)) (fun _=>rfl) u (price p d a b (held (B.layer (w n)) S) (F (w n)) (G (w n)))
   -- lift requires AddGroup M? `lift` binder implicit M? p at Tickets no instance? test
   unfold Deck.see Deck.cap; simp_rw [he,splitting (lift p) (lift p) (fun x:C× Ticket B.clan w=>(x.1,x.2.target)) (fun _=>rfl)]
   refine split_flow _ u (fun x y hp=>?_)
   change Deck C B.clan w at x y
   change Tendsto (fun n=>price p d a b _ _ _ (x.see n) (y.see n)) _ (𝓝 (price p d a b S f g x.cap y.cap))
   let t := x.fee
   have hl (a): Tendsto (fun i=> F (w i) ((a,-channel (x.see i))::x.see i)) atTop (𝓝 (f ((a,-channel x.cap)::x.cap))) :=by
       simp_rw [Deck.price,Deck.value]; apply (hf.pilots w hw ((a,x.fee.negative)::x) ?_)
       intro n; change channel ((a,_)::x.see n)=0; rw [channel_cons,Deck.price]; exact neg_add_cancel _
   have hr(a): Tendsto (fun i=>G (w i) ((a,channel (x.see i))::y.see i)) atTop (𝓝 (g ((a,channel x.cap)::y.cap))) :=by
       simp_rw [Deck.price,Deck.value]; apply (hg.pilots w hw ((a,x.fee)::y) ?_); intro n
       change channel ((a,(x.fee).f n)::y.see n)=0; rw [←Deck.price,channel_cons,← channel_plus]; apply Eq.trans (channel_move (List.Perm.trans (l₂:=(x++y).map (fun u=>(u.1,u.2.f n))) ?_ (hp.map (fun u=>(u.1,u.2.f n))))) (hu n)
       unfold Deck.see; rw [List.map_append]
   unfold price; refine Tendsto.add ((Tendsto.div_const ?_ _).mul ((tendsto_const_nhds.mul (hl a)).mul (hr b))) ((Tendsto.div_const ?_ _).mul ((tendsto_const_nhds.mul (hl b)).mul (hr a)))
   · simp_rw [Deck.price,Deck.value]; exact follows w hw x.fee.negative hs a b ha hb
   simp_rw [Deck.price,Deck.value]; exact follows w hw x.fee hs a b ha hb

lemma plus (hf:Copies B.clan F f)(hg:Copies B.clan G g): Copies B.clan (F+G) (f+g):= ⟨fun n=>(hf.clear n).add (hg.clear n),hf.quiet.add hg.quiet,fun g h v hv=> (hf.pilots _ h v hv).add (hg.pilots _ h v hv)⟩
lemma minus (hf:Copies B.clan F f)(hg:Copies B.clan G g): Copies B.clan (F-G) (f-g):=⟨fun n=>(hf.clear n).sub (hg.clear n),hf.quiet.sub hg.quiet,fun g h v hv=> (hf.pilots _ h v hv).sub (hg.pilots _ h v hv)⟩
lemma scale (hf:Copies B.clan F f)(c : ℂ): Copies B.clan (c•F) (c•f):=⟨fun n=>(hf.clear n).scale c,hf.quiet.scale c, fun g h v hv=> tendsto_const_nhds.mul (hf.pilots _ h v hv)⟩
lemma copies_eq (hf:Copies B.clan F f)(hg:Copies B.clan G g)(h:∀ n:ℕ,F n= G n) : f=g:=by
   rw [funext h] at hf; funext v; by_cases hv:channel v=0
   · obtain ⟨u,rfl,h⟩:= Snap.ships B v tendsto_id hv; exact tendsto_nhds_unique (hf.pilots id tendsto_id u h) (hg.pilots id tendsto_id u h)
   rw [hf.quiet v hv,hg.quiet v hv]
end Copies
end YM.MSbar.Loops

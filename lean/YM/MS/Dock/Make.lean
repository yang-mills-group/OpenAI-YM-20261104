import YM.MS.Dock.Hearth
/-!
# algebraic existence of Joint response after dimensional Laurent program

No proof of running coupling in these definitions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dock
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F Z J L:Flats G}{K U:Mob G}{f g p q:Coat G}{b c:Bool}{t r:ℤ}{n h ℓ:ℕ}{i:ℂ}
structure Coal (b:Bool)(h:ℕ)(g r:ℤ)(J:Flats G): Prop where
   eye:ClockD b g r J
   real: Stay h J
   force: Return J 0 h
lemma engine (X:Flats G)(T:Flats G)(hv:ClockD b t r X)(ht:Vibe n X T)(he:Return X f n)(hp:Stay n T):∃ Y:Flats G, ∃ p:Coat G, Joint n T Y f p∧ClockD b t r Y∧ Cap0 b t r p:= by
   obtain ⟨m,hH⟩:=tallP ( Moony.toast (clockMoon hv)); obtain hz:= correspondent hH ht hp; let v:= Mint m X; let Q:= X-Finsupp.single 0 v; have hQ:=mintCap hv hH; have hy:Count v n:= minted_home hH ht hp; have hF: ClockD b t r Q := fun i=> (hv i).sub (Cap0.heap.single hQ 0 i)
   refine ⟨Q,-v, {advance:=?_, toll:=hz,wet:= Moony.toast (clockMoon hF), back:=fun i=> (hy i).neg, ice:=?_, worth:= hQ.fine.tune.mer.neg, sip:=?_},hF,hQ.neg⟩; · simpa only [sub_zero] using vibe_sub ht (vibe_root hy)
   · exact (cone G).neg_mem (minted m X)
   simpa only [sub_eq_add_neg,Q] using sip_sub he (sip_root hy) -- Q simp both maybe
lemma run (h:Coal b n t r J)(hp: Count f n)(hv:Cap0 b t r f): ∃ X:Flats G, ∃ p:Coat G, Joint n J X f p ∧ ClockD b t r X∧Cap0 b t r p:= by
   obtain ⟨H0,H1,H2⟩:= scooter h.eye h.force; let V:= wheels J n+Finsupp.single 0 f; have H : Vibe n V J:= (by unfold V; simpa only [add_zero] using vibe_plus H0 (vibe_root hp)); have Hx: Return V f n:= (by unfold V; simpa only [zero_add] using sip_plus H2 (sip_root hp)); exact engine V _ (Cap0.heap.plus H1 (Cap0.heap.single hv 0)) H Hx h.real
-- cyc RHS stock coal
abbrev step0 (G:Gauge):= CycleN (A0 G 0)
lemma mine (hp:ClockD b t r F)(hr:Stay n F): Coal b n t (r-2) (step0 G F):= by
    refine ⟨ fun i=>⟨blazeG (b:=b) (fun i=>(hp i).fine) i, capC r (clockCap hp) ( clockMoon hp ) (c_bo 0) i ⟩,Cit hr ( clockMoon hp) (c_bo 0) (a:=4) (by ring),?_⟩; unfold Return step0 CycleN; rw [bland zero_lt_one]; simp_rw [Pi.zero_apply,← cert,map_zero]; exact Eventually.of_forall fun i _ _=> tendsto_const_nhds -- check simp Finsupp
lemma Cycle_t (h:Pact X F) : Pact (step0 G X) (step0 G F):= same_jump h (fun i=> feeD i • port i (A0 G 0)) _
lemma coalGather (hp:Cap0 b t r f)(hl:r<0): Spotty f 0:= by
   apply ( (pact0 (F:=.single 0 f) ⟨ r,hl, ( washed (grade r G)).single hp.cap 0⟩ ) 0).mono; intro i hi; rwa [Finsupp.single_eq_same] at hi -- eventual f
abbrev Bob (b:Bool)(n:ℕ)(i:ℤ)(r:ℤ)(J X:Flats G)(f p:Coat G): Prop:= Joint n (J+step0 G X) X f p∧ ClockD b i r X∧ Cap0 b i r p
lemma pact_sym (h:Pact X Y): Pact Y X:=fun i=>(h i).symm
lemma factory' (k:ℕ)(hh: r ≤ (k:ℤ)) (he:Coal b n t r J)(hv: Count f n)(hp:Cap0 b t r f) : ∃ X: Flats G,∃ p:Coat G, Bob b n t r J X f p:= by
   induction k using Nat.strong_induction_on generalizing r J f with
   | h k ih=>
      obtain ⟨V,p,Ht,H,pH⟩:= run he hv hp; obtain hm := mine H Ht.toll; by_cases hy:r<2
      · refine ⟨V,p,Ht.via ?_,H,pH⟩; have hp := pact0 (F:=step0 G V) ⟨ _,(by omega:r-2<0),clockCap hm.eye⟩; refine pact_sym (fun i=>?_); filter_upwards [hp i] with j hj; simp only [Finsupp.add_apply,Pi.add_apply,hj, Finsupp.zero_apply,Pi.zero_apply,add_zero] -- orientation ? Pact J J+d via via expects Pact J (J+d) invert
      obtain ⟨W,f',hE,hF,hp⟩:=ih (k-1) ( Nat.sub_one_lt (by omega)) (show r-2≤ ((k-1:ℕ):ℤ) by omega) hm (f:=0) (fun _=>Home.zero n) Cap0.zero; refine ⟨ V+W, p+f', ?_,Cap0.heap.plus H (clockTrans hF (by omega:r-2≤r)), pH.add ( hp.collects (by omega))⟩; obtain ht:=Ht.plus hE; simpa only [add_zero,map_add] using ht
lemma factory (h:Coal b n t r J)(hp:Count f n)(hf:Cap0 b t r f):∃ X:Flats G,∃ p:Coat G, Bob b n t r J X f p:= factory' r.toNat (by omega) h hp hf
end YM.MS.Dock

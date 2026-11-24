import YM.MS.Awning.Burn
/-!
# External polynomial degrees. Finite value tests.
Linear constraints can be tested at any stage of Laurent/ODE construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Awning
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Signal Book Convolve
open scoped Topology ContDiff Interval
variable {G:Gauge}{k m n h d:ℕ}{q r t:ℤ}{b:Bool}{F J X:Flats G}{f:Coat G}
open Dock Emit Outlook Halo
abbrev Ran (q:ℤ)(V:Flats G):= SeedP (fun f=> To f (CapAir q G)) V
lemma Engine (hv:ClockD b t r X)(ht:Vibe n X J)(he:Return X f n)(hp:Stay n J)(hx:Ran q X):∃ Y:Flats G, ∃ p:Coat G, Joint n J Y f p∧ClockD b t r Y∧ Cap0 b t r p∧ Ran q Y:= by
   obtain ⟨m,hH⟩:=tallP ( Moony.toast (clockMoon hv)); obtain hz:= correspondent hH ht hp; let v:= Mint m X; let Q:= X-Finsupp.single 0 v; have hQ:=mintCap hv hH; have hy:Count v n:= minted_home hH ht hp; have hF: ClockD b t r Q := fun i=> (hv i).sub (Cap0.heap.single hQ 0 i)
   refine ⟨Q,-v, {advance:=?_, toll:=hz,wet:= Moony.toast (clockMoon hF), back:=fun i=> (hy i).neg, ice:=?_, worth:= hQ.fine.tune.mer.neg, sip:=?_},hF,hQ.neg,?_⟩; · simpa only [sub_zero] using vibe_sub ht (vibe_root hy)
   · exact (cone G).neg_mem (minted m X)
   · simpa only [sub_eq_add_neg,Q] using sip_sub he (sip_root hy)
   have H:= MintC hH ( CapAir q G ) (Needed q) hx; intro i; exact ((hx i).and ((washed ( CapAir q G )).single (Eventually.of_forall H) 0 i)).mono fun s hs=> ( CapAir q G ).sub_mem hs.1 hs.2
lemma Run (h:Coal b n t r J)(hp: Count f n)(hv:Cap0 b t r f)(hq:Ran q J)(hU:To f ( CapAir q G )): ∃ X:Flats G, ∃ p:Coat G, Joint n J X f p ∧ ClockD b t r X∧Cap0 b t r p∧Ran q X:= by
   obtain ⟨H0,H1,H2⟩:= scooter h.eye h.force; let V:= wheels J n+Finsupp.single 0 f; have H : Vibe n V J:= (by unfold V; simpa only [add_zero] using vibe_plus H0 (vibe_root hp)); have Hx: Return V f n:= (by unfold V; simpa only [zero_add] using sip_plus H2 (sip_root hp)); refine Engine (Cap0.heap.plus H1 (Cap0.heap.single hv 0)) H Hx h.real ((washed ( CapAir q G )).plus (fun i=>?_) ( (washed _).single hU 0)); rw [ loopy ]; filter_upwards [hq i,( h.eye i ).fine.tune.mer.price,vamp_up n i] with w hw hH HZ; exact Mell.road ( CapAir _ G ) (Needed q) hw hH HZ
lemma Factory (k:ℕ)(hh: r ≤ (k:ℤ)) (he:Coal b n t r J)(hv: Count f n)(hp:Cap0 b t r f)(hQ:Ran q J)(hf: To f ( CapAir q G )) : ∃ X: Flats G,∃ p:Coat G, Bob b n t r J X f p∧Ran q X:= by
   induction k using Nat.strong_induction_on generalizing r J f with
   | h k ih=>
      obtain ⟨V,p,Ht,H,pH,hV⟩:= Run he hv hp hQ hf; obtain hm := mine H Ht.toll; by_cases hy:r<2
      · refine ⟨V,p,⟨Ht.via ?_,H,pH⟩,hV⟩; have hp := pact0 (F:=step0 G V) ⟨ _,(by omega:r-2<0),clockCap hm.eye⟩; refine pact_sym (fun i=>?_); filter_upwards [hp i] with j hj; simp only [Finsupp.add_apply,Pi.add_apply,hj, Finsupp.zero_apply,Pi.zero_apply,add_zero]
      obtain ⟨W,f',⟨hE,hF,hp⟩,ht⟩:=ih (k-1) ( Nat.sub_one_lt (by omega)) (show r-2≤ ((k-1:ℕ):ℤ) by omega) hm (f:=0) (fun _=>Home.zero n) Cap0.zero (ignite H hV) (( washed _ ).zero); refine ⟨ V+W, p+f', ⟨?_,Cap0.heap.plus H (clockTrans hF (by omega:r-2≤r)), pH.add ( hp.collects (by omega))⟩,( washed _ ).plus hV ht⟩; obtain ht:=Ht.plus hE; simpa only [add_zero,map_add] using ht
lemma Run0 {A B:T (Flats G)} {P Q:T (Coat G)} (h:comet n t A Q B P)(ht: Badge false (Q 0) n t)(hp: To ( Q 0 ) ( CapAir q G )): Ran q (B 0):= by
    obtain ⟨⟨r,Ht,V,H⟩,ht'⟩:= h 0; rw [show platform A 0 B=0 from ?_] at Ht; swap; unfold platform shortM; simp
    obtain ⟨w,hB⟩:= ht.stock; obtain ⟨X,p,⟨hX,hM,hq⟩,hp⟩:= Factory (b:=false) w.toNat (by omega:w≤ (w.toNat:ℤ)) (coal_zero ..) ht.born hB ( show Ran q 0 from fun i=> (washed _).zero ) hp; obtain h:= super hX Ht (fun _=>EventuallyEq.rfl) EventuallyEq.rfl hM V
    exact fun i=> ((h.1 i).and (hp i)).mono fun k hk=> hk.1 ▸ hk.2
-- seed rank bound and projection
open Mach
lemma Standard {F: Mob G}(hp: kPrice F)(h:Home F n)(ht: Goods (k:ℤ) F): F∈ CapAir ( (n:ℤ)-k ) G:= by
    intro m E _ _ _ W x v; by_cases he:W.length=k
    · change (fun t:ℝ=> fieldVal (F m) W (x+t • v))∈_; have hz:= h.complete hp; unfold PriceR; rw [he,show (n:ℤ)-k-mass W+k=n-mass W from by abel ]; apply crossed; rcases lt_or_ge (n:ℤ) (mass W) with h1|h1; · rw [hz,Hem.plane h1 ]; exact form_zero _
      have heq: mass W+( ((n:ℤ)-mass W).toNat:ℤ)=n:= by omega
      rw [hz,Hem.film ((hp m E W).smooth ()) heq]; exact form_diag _ _ (by omega)
    simp_rw [ranks_off ht (sail W _) (by simpa using he) ]; exact (Bowl _).zero_mem -- ⇑ T comp
open Motif Literal Menus Land
lemma Seed0 {A:Detect.Law G}{V:Box (Mob G)}(hv:Ele h n A V): let F:= gloss (linear ( Mob G ) V) 0; To F ( CapAir ( (h:ℤ)-n ) G ):= by
    obtain ⟨hp,r,hr⟩:= hv.grows 0; intro F'; refine ( hr.fine.tune.mer.price ).mono (fun i hi=>?_); exact Standard hi (hp _) hv.Top -- `F'
variable {B: Local.Physical.Deck G}
lemma Value0 {A: Booked B}(X: MS_Data G A)(i:Plaid B h)(s y:ℝ): hereZ h ( X.marks h i 0 ) s y∈ CapAir ((h:ℤ)-(Land.read i).grade) G:= by
    have hp:= X.markOK h i; have he:= A.law h i; have hu:= RootF (hp 0); exact valueC hu.toll hu.wet _ (Needed _) ( Run0 hp ( he.grows 0 ) ( Seed0 he ))
end YM.MS.Awning

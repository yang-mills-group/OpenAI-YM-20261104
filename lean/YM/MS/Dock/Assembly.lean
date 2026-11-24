import YM.MS.Dock.Clime
/-!
# Assemble Quarters into overarching perturbative series at formal ζ level
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dock
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I A:Type}{G:Gauge}{X Y F J:Flats G}{b c:Bool}{t v r:ℤ}{n m h ℓ:ℕ}{i:ℂ}{f g p:Coat G}
abbrev Pin:=ℕ→ Prop
abbrev Drive (G:Gauge):= ℕ→ (ℕ→ Flats G) → Flats G
def sings (b:Bool) (t:ℤ) (h:ℕ) (f:Coat G) (C: Prop) (J:Flats G)(X:Flats G)(p:Coat G): Prop:= ((∃ r:ℤ,Bob b h t r J X f p)) ∧ (C→ X=0)
abbrev PathD (D:Drive G)(p:ℕ→ Flats G)(a: T (Coat G))(P:T (Coat G))(K:Pin)(b:Bool)(t:ℤ)(h:ℕ)(i:ℕ) : Prop := sings b t h (a i) (K i) (D i p) (p i) (P i)
abbrev Region (D: Drive G) (K:Pin)(b:Bool)(t:ℤ)(h:ℕ)(a P: T (Coat G))(F:T (Flats G))(n:ℕ): Prop:= ∀ i<n,PathD D F a P K b t h i
def lowD (D E:Drive G): Prop:=∀ n f p,(∀ i<n,Pact (f i) ( p i))→ Pact (D n f) ( E n p)
lemma sings.via {P:Prop}(hP : sings b t h f P X Y p)(hp:Pact X J): sings b t h f P J Y p:= by obtain ⟨⟨n,hp',hP⟩,H⟩:= hP; exact ⟨ ⟨_, hp'.via (common hp (fun _=>EventuallyEq.rfl)), hP⟩,H ⟩
variable {P M:Pin}{D E:Drive G} {B a c' q:T (Coat G)}{F H:T ( Flats G)}
structure Ethics (D:Drive G)(P:Pin)(B: T (Coat G))(b:Bool)(t:ℤ)(h:ℕ): Prop where
   low: lowD D D
   rise n F q : Region D P b t h B q F n→∃ X: Flats G,∃ p:Coat G, sings b t h ( B n) (P n) (D n F) X p
lemma Ethics.rebar (h:Ethics D P B b t n)(m:ℕ): ∃ q F, Region D P b t n B q F m:= by
   induction m with
   | zero=> exact ⟨0,0,fun i hi=>by omega⟩
   | succ m ih=>
      obtain ⟨q,F,H⟩:=ih; obtain ⟨X,p,hX⟩:=h.rise m F q H; let G:= Function.update F m X; let Y:= Function.update q m p; refine ⟨Y,G,fun i hi=>?_ ⟩; have he:{k:ℕ}→k≤m→ Pact (D k F) ( D k G):= fun {k} hk=> h.low _ _ _ (by intro j hj; rw [show G j= F j from Function.update_of_ne (by omega : j≠m) ..]; intro j; exact EventuallyEq.rfl); unfold PathD; by_cases hL:i=m; · subst i; unfold G Y; simp only [Function.update_self]; exact hX.via (he le_rfl)
      rw [show G i=_ from Function.update_of_ne hL .., show Y i=q i from Function.update_of_ne hL ..]; exact sings.via (H i (by omega)) (he (by omega))
lemma reune (H₀: Region D P b t h B a F m)(H₁: Region E M b t h B q H n)(he:lowD D E): ∀ i< min m n,Pact ( F i) (H i)∧a i=q i:= by
   intro k; induction k using Nat.strong_induction_on with
   | h k ih=>
      intro hk; obtain ⟨⟨s,hu,hA,hp⟩,hq⟩:= H₀ k (by omega); obtain ⟨⟨v,hv,hY,hX⟩,ha⟩:= H₁ k (by omega); exact super hu hv (pact_sym ( he k F H ( fun i hi=> (ih i hi (hi.trans hk)).1))) EventuallyEq.rfl hA hY
abbrev LPT (D:Drive G)(K:Pin)(b:Bool)(t:ℤ)(h:ℕ)(B: T (Coat G))(F:T ( Flats G))(q:T (Coat G)): Prop:= ∀ n:ℕ, PathD D F B q K b t h n
lemma Ethics.pow (hP: Ethics D P B b t h): ∃ F q,LPT D P b t h B F q:= by
    choose u V hu using Ethics.rebar hP; let F (i:ℕ) := V (i+1) i; let Q(i:ℕ):= u (i+1) i; refine ⟨ F,Q,fun i=>?_⟩; exact sings.via (hu (i+1) i (by omega)) ( hP.low i (V (i+1)) F (fun j hj=> ( reune (hu (i+1)) (hu (j+1)) hP.low j (by omega)).1 ))
lemma LPT.unique (hx:LPT D P b t h B F q)(hp:LPT E M b t h B H a)(ht:lowD D E) : q=a∧∀ i,Pact (F i) (H i):= by
    have hh (i:ℕ):= reune (fun j (h:j < i+1)=> hx j) (fun j (h:j < i+1)=> hp j) ht i (by omega); exact ⟨ funext fun i=> (hh i).2,fun i=> (hh i).1⟩
end YM.MS.Dock

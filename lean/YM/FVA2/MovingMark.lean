import YM.FVA2.WeftMark
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
variable (hv:Frozen ( awaken g a d ) V x)
variable {Z: Set ℝ}(H:IsOpen Z)
variable (hA:PathAlong g d x Z)
variable {w y: Finset W}
local notation "Ψ"=> field (Landau.parity (A:=Axis) (C:=G.ColorIndex))
section
variable {g d}
-- summation in form of functions proper
lemma direct.whole {F H:I→ℝ→ℂ}{p q:ℂ}(A:Finset I)(hp:∀ i∈A,direct Z p q (F i) (H i)): direct Z p q (fun x=>∑ i∈A,F i x) (fun x=>∑ i∈A,H i x):= by simp_rw [← Finset.sum_apply ]; apply direct.bulkD _ _ _ hp
lemma batch {F H:I→ Glade G ℝ}(A:Finset I) (hp:∀ i∈A, grade Z d g w ( F i ) ( H i )) : grade Z d g w (∑ i∈A,F i) (∑ i∈A, H i) := by intro a t; simp_rw [Finset.sum_apply]; apply direct.whole; exact (fun i h=> hp i h a t)
lemma direct.scatterD {V:Type} (p b:ℂ)(s:Sector V)(a:Legs V)(F H:ℝ→Shared V ℂ)(he:∀ l r, Split l r a → direct Z p b (fun t=> F t l r) (fun t=> H t l r)): direct Z p b (fun t=>scatter s a (F t)) (fun t=>scatter s a (H t)):= by induction a generalizing F H with| nil=> exact he _ _ .nil | cons x a ih=> exact ih _ _ ( fun i j hp=> (he _ _ hp.left).sumD ((he _ _ hp.right).scales _) )
variable {k:ℕ}
include hu hv h H
lemma sails (hw:w.Nonempty)(t:ℕ) (A:Legs (Lane4 G))(hq:∀ L: Legs (Lane4 G), L.length > A.length → Pulled Z ( U w t ) ( V w t ) ( liftP w g ) ( strike ( peak w d g ) ( net L ) ) L): Pulled Z ( sailP ( fun _=>planeF ) Δ ( U w t ) ) ( sailP (fun _=>planeF ) Δ ( V w t ) ) ( liftP w g ) ( strike ( peak w d g ) ( net A ) ) A:= by
    intro s; let F (X:Rake.Dance G ℝ W)(i:ℝ)(q:QP):= trc ( PlanetD G s ) q ( X w t i s ) A; apply direct.majorize H ( loopP h hu s hw t A ) ( loopP h hv s hw t A ); intro i; simp_rw [ at_trc ]; refine direct.whole _ (fun j hj=>?_); refine direct.whole _ (fun l _=>?_); let k:= ( j,i )::( l,-i )::A; let p:= PlanetD G s; obtain hz:= hq k (by simp [k]) s; simp only [k,net_cons,add_neg_cancel_left] at hz; exact hz.scales _
include hA
lemma walks {t q:ℕ}(hy:y∈picks w)(he:grade Z d g y (U y t) (V y t))(hf: grade Z d g (w\y) ( U ( w\y ) q ) ( V ( w\y ) q )): grade Z d g w ( regionC (fun _=>planeF) ( rootX x y-rootX x w ) Δ (U y t) ( U ( w \ y ) q ) ) ( regionC (fun _=>planeF) (rootX x y-rootX x w) Δ (V y t) ( V ( w \ y ) q ) ):= by
   intro A s; simp_rw [powered]; refine direct.scatterD _ _ _ _ _ _ ( fun L R hp=> ?_ ); refine direct.whole _ ( fun i _=>?_ ); refine direct.whole _ (fun j _=> ?_); exact direct.majorize H ( fuelM h hu hy t q s ) (fuelM h hv hy t q s) ( fun t=> central hu hv hA hy _ _ he hf _ _ hp )
omit hA hu hv h H
lemma attends {p:ℕ} (hf:grade Z d g w (U w p) (V w p)) : grade Z d g w ( expJ Δ ( approach Υ S k ) ( U w p )) ( expJ Δ ( approach Υ S k ) (V w p) ):= by
    intro A s; unfold expJ tree; refine direct.scatterD _ _ _ _ _ _ ( fun L R he=>?_ ); unfold attaches; dsimp only; refine direct.whole _ (fun i _=> ?_); refine direct.whole _ (fun j _=> ?_); let Q:= net L;
    obtain hi:= hf ((i,Q)::R) s; obtain hj:= hf ((j,Q)::R) s; rw [neg_neg (net L)]; simp only [net_cons,Q,split_net he] at hi hj; apply direct.sumD (g:= fun t=> _) (f:=fun t=> _)
    · exact (hj.scales ( (cross ( parity j ) (degree (field parity ) L))* approach Υ S k 0 s ((i,-net L)::L) )).scales ( Δ 0 s i j (-net L) )
    exact (hi.scales ( (cross ( parity i ) (parity j ^^ degree (field parity ) L))* approach Υ S k 0 s ((j,-net L)::L) )).scales ( Δ 0 s i j (net L) )
include hA h hu hv H
lemma supply (_he:2≤w.card) (t:ℕ)(hp:∀ s⊂w,∀ p,grade Z d g s ( U s p ) ( V s p ))(hc:∀ p<t,grade Z d g w ( U w p ) ( V w p )):grade Z d g w ( Src x (fun _=>planeF) Δ Δ (approach Υ S) U w t ) ( Src x (fun _=>planeF) Δ Δ (approach Υ S) V w t ):= by
    have hz: grade Z d g w ( lonely Δ ( approach Υ S ) ( U w ) t ) ( lonely Δ ( approach Υ S ) ( V w ) t ) := batch _ (fun i hi=> attends (hc i ( Finset.mem_Ico.mp hi|>.2 ) ) ); have ht:=batch (w:=w) (picks w) ( fun i hi=> batch ( Finset.antidiagonal t ) (fun j _=> walks h hu hv H hA hi (hp _ ( n_small hi|>.1 ) j.1) (hp _ ( n_small hi|>.2.2.2 ) j.2)) ); exact fun a s=> (hz a s).sumD (ht a s)
-- choose collect caps both for induction. close Λ permits implicit.F.R. quadrature.
lemma movement (w: Finset W)(t:ℕ): grade Z d g w ( U w t ) ( V w t ):= by
    induction w using Finset.strongInductionOn generalizing t with| _ w ih=>
      rcases lt_or_ge w.card 2 with he|he
      · obtain hq|hq:= show w.card=0 ∨ w.card=1 from (by omega);
        · rw [card_eq_zero.mp hq,hu.1,hv.1]; intro p q i hi; simpa using (hasDerivAt_const i (0:ℂ))
        obtain ⟨j,rfl⟩:= card_eq_one.mp hq; rw [hu.2.1,hv.2.1]; intro p q i hi; unfold liftP peak key rootsRow awaken; by_cases hp:g=j;
        · subst g; simp [ multiple, Finset.mem_singleton, derive, rise, poleDer ]; exact hasDerivAt_const i _
        simp [ hp, Ne.symm hp, multiple, strike_zero ]; exact hasDerivAt_const i _
      have hw:= Finset.card_pos.mp ( show w.card>0 from by omega ); induction t using Nat.strong_induction_on with| h t hh=>
        let X(K:Rake.Dance G ℝ W):= rhs x (fun _=>planeF) Δ Δ (approach Υ S) K w t; obtain hz:= hu.2.2 w he t|>.2.2; obtain hk := hv.2.2 w he t |>.2.2; change U w t=river ( X U ) at hz; change V w t= river ( X V ) at hk;
        obtain ⟨P,hP⟩:= Vane.founded (passage a h) hu hw t |>.1; obtain ⟨Q,hQ⟩:= Vane.founded (passage _ h) hv hw t |>.1; intro L; suffices HE : ∀ k (l:Legs ( Lane4 G )),max P Q < k+l.length → Pulled Z ( U w t ) ( V w t ) ( liftP w g ) ( strike ( peak w d g ) ( net l ) ) l from HE (max P Q+1) L (by omega)
        intro k; induction k with
        | zero=> intro l hl p i hi; simp_rw [ show ∀ i, U w t i p l=0 from fun i=> hP i p l (by omega), hQ i p l (by omega) ]; simpa using ( hasDerivAt_const i (0:ℂ) )
        | succ k he'=> intro l hl p; rw [ hz, hk ]; apply direct.majorize H ( riverP h hu he l t ) (riverP h hv he l t ); exact fun u=> ( sails h hu hv H hw t l ( fun L hL=>he' L (by omega) ) u ).sumD ( supply h hu hv H hA he t ih hh l u )
end
end YM.FVA2.Poesy

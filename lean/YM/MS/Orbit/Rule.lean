import YM.MS.Orbit.LimitZ
/-!
# Grammar list of marks. Ordered pick rule.Past no lower rank issue. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book Convolve
open scoped Topology ContDiff Interval
variable {I G' E W:Type}[LinearOrder W]{G:Gauge}{K:Planet G I}{Z:Lin I}{X:ℕ→I→ Law G}{B:Rake.Site G I}
    {v:I→Cover} {S:Finset W}{Y:H_defect G I}{F H:Rake.Dance G I W}
def archB (Z:Lin I)(x: Faces I)(K:Planet G I)(F:Rake.Dance G I W)(S:Finset W)(i:ℕ) := ∑ p∈ picks S,∑ j∈ antidiagonal i, zip2 Z K x x (F p j.1) (F ( S \ p ) j.2)
def campus (Z:Lin I)(x:Faces I)(K:Planet G I)(B:Rake.Site G I)(Y:H_defect G I)(V:Rake.Site G I)(F:Rake.Dance G I W)(S:Finset W)(n:ℕ):= lonely K B V n+ foam Z K Y V x n 0 + archB Z x K F S n
abbrev Seeds (G:Gauge)(I W:Type):= Finset W→ℕ→I→Law G
variable {Q:Seeds G I W}
def Crew (Z:Lin I)(K:Planet G I)(B:Rake.Site G I)(Y:H_defect G I)(x:Faces I)(Q:Seeds G I W)(F:Rake.Dance G I W): Prop:= F ∅=0 ∧ ∀ S:Finset W,S.Nonempty→∀ i, Clocked (zip0 Z K x) ( Q S i ) ( F S i ) (campus Z x K B Y ( F S ) F S i)
lemma SteadyCrew {n:ℕ}{X V:Rake.Site G I}(hV:∀ s ⊂ S,F s=H s)(hp:∀ i<n,X i=V i): campus Z v K B Y X F S n= campus Z v K B Y V H S n:= by
    unfold campus archB; refine congr_arg₂ (·+·) (congr_arg₂ (·+·) ?l ?r) ?a; · exact Finset.sum_congr rfl fun i hi=> congr_arg _ (hp i ( early _ _ _ hi|>.2 ))
    · exact Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j hj=> congr_arg _ (hp j ( early _ _ _ hj|>.2))
    exact Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j hj=> congr_arg₂ (zip2 Z K v v) (congr_fun ( hV i ( n_small hi|>.1 ) ) j.1) (congr_fun ( hV _ ( n_small hi|>.2.2.2)) j.2)
lemma soloP (h:Crew Z K B Y v Q F)(he:Crew Z K B Y v Q H): F=H:= by
   funext S; induction S using Finset.strongInductionOn with| _ S hS=>
      by_cases hp:S.Nonempty; swap; · rw [Finset.not_nonempty_iff_eq_empty.mp hp,h.1,he.1]
      funext n; induction n using Nat.strong_induction_on with| h n ih=> obtain hz := h.2 S hp n; rw [SteadyCrew hS ih] at hz; exact modal_uniq ( β_motor (engineV ..) ) hz (he.2 S hp n)
lemma campusK {F:Rake.Dance G I W}{T:Rake.Site G I} (h:Glow K)(hq:∀ i:ℕ, Knits ( B i ))(hp:∀ i:ℕ,∀ z, Knits ( Y z i ))(hf:∀ S' ⊂ S,∀ i, Knits ( F S' i )) (k:ℕ)(hx:∀ i<k, Knits ( T i )): Knits ( campus Z v K B Y T F S k ) := by
   refine knit_plus ( knit_plus ( knit_sum _ fun i hi=> knit_tree h (hq _) ( hx _ (early _ _ _ hi|>.2) ) ) ?a ) ?b; · exact knit_sum _ fun i hi=> knit_sum _ fun j hj=> knit_zip h (hp (k-j) i) ( hx _ ( early _ _ _ hj |>.2) )
   exact knit_sum _ fun i hi=> knit_sum _ fun j hj=> knit_zip h (hf i (n_small hi|>.1) j.1) (hf (S\i) (n_small hi|>.2.2.2 ) j.2 ) -- remove implicit H
lemma growM (Z:Lin I)(K:Planet G I)(v:Faces I)(h:Glow K)(hp:∀ i, Knits ( B i ))(hY:∀ z i, Knits (Y z i))(hQ:∀ S,Caps ( Q S )) : ∃ F:Rake.Dance G I W, Crew Z K B Y v Q F ∧ ∀ S i, Knits (F S i):= by
   let R(s:Finset W)(F':Finset W→ℕ→ Glade G I)(V:ℕ→ Glade G I): Prop:= if s.Nonempty then ∀ i, Clocked (zip0 Z K v) ( Q s i ) ( V i ) (campus Z v K B Y V F' s i) else V=0; suffices he: ∃ f,∀ i,R i f (f i) ∧ ∀ n,Knits ( f i n ) by
      obtain ⟨f, hf⟩:= he; refine ⟨ f,?_,fun s i=> hf s|>.2 i ⟩; exact ⟨ by simpa [R] using hf ∅|>.1, fun S hp=> by simpa only [R,if_pos hp] using (hf S).1⟩
   refine drawer (r:=(· ⊂ ·)) ( D:=fun S F=>∀ i, Knits (F i)) ( R:=R ) ?_ ?_ ?_
   · exact wellFounded_lt
   · intro i f g h F; unfold R; simp_rw [ SteadyCrew h ( X:=F ) (V:=F) (fun i j=>rfl) ]; -- `$ℕ,k placeholder`
   intro i f hs; unfold R; by_cases he : i.Nonempty; swap; · exact ⟨0,(by rw [ if_neg he ]),fun _=>knit0 ..⟩
   simp_rw [if_pos he]; let U:= zip0 Z K v; let V (n:ℕ)(F:ℕ→ Glade G I)(H:Glade G I):= Clocked U (Q i n) H (campus Z v K B Y F f i n); have h0 : ∃ T',∀ i,V i T' ( T' i ) ∧ Knits (T' i):= drawer (r:=(· < ·)) ( R:=V ) ( D:=fun i F=> Knits F ) Nat.lt_wfRel.wf (fun j f g he T'=> by unfold V; rw [SteadyCrew (fun s h=> rfl) he]) ( fun j F h0=> (gen_zip0 Z h v).perfect (hQ i j) ( campusK h hp (fun i v=> hY v i) hs j h0 ) ); obtain ⟨ T',hh⟩:= h0; exact ⟨ T',fun i=> hh i|>.1,fun i=> hh i|>.2⟩
end YM.MS.Orbit

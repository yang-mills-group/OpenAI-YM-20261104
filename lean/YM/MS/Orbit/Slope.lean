import YM.MS.Orbit.Sales
/-!
# Streams. structural generation for B and D_z. Deck grammar. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Rake Flux Cog Wire Book Convolve
open scoped Topology ContDiff Interval
variable { I E:Type}{G:Gauge}{K:Planet G I}{Z:Lin I}
abbrev CPlan (Z:Lin I)(K:Planet G I):= click Z false (fun _=> 0) K
abbrev ubB (i j:ℕ):= Domain.paths i j
lemma early (n j i:ℕ)(h:i∈ ubB n j): j≤ i ∧ i<n := Finset.mem_Ico.mp h
-- staged Rec.Planner
variable {H:Type*}{A:Type*}[Inhabited A]
lemma drawer {r:H→H→Prop}[∀ i j,Decidable (r i j)]{D:H→A→Prop}{R:H→(H→A)→ A→Prop} (h:WellFounded r) (hp:∀ i f g,(∀ j,r j i→ f j=g j )→ ∀ x,R i f x ↔ R i g x)(hx:∀ i f, (∀ j,r j i→D j (f j))→ ∃ y,R i f y ∧ D i y) : ∃ f,∀ i:H,R i f (f i) ∧ D i (f i):= by
    classical
    let F (i:H) (f:H→A): A:= Classical.epsilon (fun y=> R i f y∧ D i y); let P (i:H)(g: ∀ j:H, r j i→ A): (H→A):= fun j:H=> if h:r j i then g j h else default; let Y(i:H):= h.fix (C:=fun _=>A) (fun i g=> F i (P i g)) i; refine ⟨Y,fun i=>?_⟩; induction i using h.induction with | h i ih=>
       rw [ show Y i= F i ( P i (fun j _=> Y j) ) from h.fix_eq _ _ ]; let X:= P i (fun j _=> Y j); have he(j:H)(hh:r j i): X j=Y j:= by unfold X P; rw [dif_pos hh]; -- rfl
       obtain ⟨hu,hk⟩:= Classical.epsilon_spec ( hx i X (fun j hv=> he j hv|>.symm ▸ ( ih j hv).2) ); exact ⟨( hp i X Y he _).mp hu,hk⟩
-- BULK
variable {X:ℕ→I→ Law G}{S V:Rake.Site G I}
def pathU (f:E→ E→ E) (n k:ℕ)[AddCommMonoid E](B D:ℕ→ E): E:= ∑ i∈ ubB n k, f (B (n-i)) ( D i )
abbrev groups (K:Planet G I)(U V:Rake.Site G I)(n):= pathU (expJ K) n 1 U V
def Script (Z:Lin I)(K:Planet G I)(X:ℕ→ I→ Law G)(S:Rake.Site G I): Prop:= S 0=0∧∀ n:ℕ,0<n→ Clocked (CPlan Z K) (X n) (S n) ( ((2:ℂ)⁻¹) • groups K S S n )
lemma clickE (b:Bool)(v:I→Cover)(hp:Glow K): LiftE ( click Z b v K ):={
   toEngine:= airEngine _ _
   tones:=fun _ h=> loopT _ _ _ h hp
   plus := fun _ _ h H=> Cplus Z b v hp h H } -- error .. before args
lemma β_motor {A:Calculator G I}(h:Rake.Engine A): motor A:=fun _ _ _=> h.degree _ _ _ -- binders
lemma g_congr {n:ℕ}(H: ∀ i<n,S i=V i): groups K S S n=groups K V V n := Finset.sum_congr rfl fun i hi=> (congr_arg₂ (expJ K) (H _ (by obtain h:=early _ _ _ hi; omega)) (H _ (early _ _ _ hi|>.2)))
lemma soloB (h:Script Z K X S)(he:Script Z K X V): S=V:= by
    funext n; induction n using Nat.strong_induction_on with| h n hp=>
       by_cases hx:n>0; swap; · rw [show n=0 from (by omega),h.1,he.1]
       obtain hu:= h.2 n hx; rw [g_congr hp] at hu; exact modal_uniq ( β_motor ( airEngine .. )) hu (he.2 n hx)
def Caps (Q:ℕ→ I→ Law G): Prop:= ∀ n,Knits ( coast0 ( Q n ))
abbrev Footprint (X:ℕ→ I→ Law G): Prop:= X 0=0∧Caps X
lemma knitB (Z:Lin I)(h:Glow K)(hp: Caps X): ∃ S,Script Z K X S∧∀ i:ℕ, Knits (S i):= by
   let R(i:ℕ)(Y:ℕ→ Glade G I)(F:Glade G I):= if i=0 then F=0 else Clocked (CPlan Z K) (X i) F ( ((2:ℂ)⁻¹) • groups K Y Y i ); have he : ∃ S:Rake.Site G I,∀ i:ℕ,R i S (S i) ∧ Knits ( S i ):= drawer (r:=(· < ·)) (D:=fun i F=> Knits F) Nat.lt_wfRel.wf (fun i f g h x=>by unfold R; rw [g_congr h]) (fun i f hx=> by
       by_cases hi:i=0; · exact ⟨ 0,by unfold R; rw [if_pos hi] ,knit0 .. ⟩
       unfold R; simp_rw [if_neg hi]; apply (clickE false 0 h).perfect (hp i); apply knit_smul ; exact knit_sum _ fun j hj=> knit_tree h ( hx (i-j) (by obtain hf:= early _ _ _ hj; omega) ) (hx j (early _ _ _ hj|>.2)) ); -- `apply stitch`
   obtain ⟨S,hV⟩:= he; refine ⟨ S, ⟨ by simpa [R] using hV 0|>.1,fun i hi=>( by simpa only [ R,if_neg (Nat.pos_iff_ne_zero.mp hi) ] using hV i|>.1 )⟩ ,fun i=> hV i|>.2⟩
lemma Batch (h:Glow K)(hp:Script Z K X S)(hu:Caps X)(i:ℕ): Knits (S i):= by obtain ⟨V,hv,hT⟩:= knitB Z h hu; rw [soloB hp hv]; exact hT i
end YM.MS.Orbit

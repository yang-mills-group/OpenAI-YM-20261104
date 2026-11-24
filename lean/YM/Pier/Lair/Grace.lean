import YM.TraceExtension.Atlas.Global
import YM.Contacts.Deck.Rigid

/-! Add nesting at ALL composites and all-r tail to the PlotX constructor, keeping O and preserves real. Extra near assumption needed for AFTER plotting (Sunk). Same F throughout. Main goal is polynomial recapture and inverse reflected pricing in stable measuring frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pier.Lair
open Function Filter Set Table Extraction Climb Analysis Ward Spec
open Trace Trace.Over Trace.Terrace Trace.Pilot MergeProof.East Next.Rank
open Next.UVStress Spin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{f : Extraction.Order}{S:Table C.book}
variable (F: Final C f S) (h:G.Simple) {H : (Bel C.book).Hierarchy}
set_option quotPrecheck false
local notation "B" => (Bel C.book)
local notation "θ" => Maxwell.Free.spin_free C.labels
local notation "τ" => (turns C)
local notation "W₀" => (Maxwell.Free.scheme C.book.grid)
local notation "W₁" => F.sector.derivatives
local notation "H₀" => Maxwell.Free.hierarchy C.labels
local notation "H₁" => F.room.kernel
local notation "τ₁" => F.sector.turns
variable {X:Scaling S}{l: Ultrafilter (ℕ×ℕ)}{Z:Arch C}{V:∀ i, Vane C i}
variable (Y:ℕ→∀ d:ℕ,change S d)
-- cheaper projection than requiring all d at all times. Enough compatible trace horizon and Dawn letter schemes through d≤4.
include F in
lemma flows (hx:Approaches (path X) (isoPanel X))
   (hY:∀ d:ℕ,Tendsto (fun i=>moveV (S:=S) d (X.U i d) (Y i d)) atTop (𝓝 1)):
     Approaches (path X) (fun i d=>(Y i d).toLinearMap):=by
   constructor; intro n v;
   let t(i:Fin n):=(v i).1
   let p(i:Fin n):(Bel C.book).Field (t i):=(v i).2
   let Q (k:ℕ)(i:Fin n):= moveV (S:=S) (t i) (X.U k (t i)) (Y k (t i)) (p i)
   have ht i : Tendsto (fun k=>Q k i) atTop (𝓝 (p i)):= Dash.arcing (hY _) (tendsto_const_nhds (x:=p i))
   have he:= flowing H₁ H₀ X hx Q p ht
   refine he.congr (fun k=> (smoothZoom (H₁).smooth _ (X.positive k)).sub (smoothDisc (T:=Bel C.book) (H₀).smooth _)) (Eventually.of_forall (fun k x _=> ?_))
   change S.classMoment S t _ (fun i=>X.U k (t i) (Q k i)) - _= S.classMoment S t _ (fun i=>Y k (t i) (p i)) - _
   rw [show (fun i=>X.U k (t i) (Q k i))=(fun i=>Y k (t i) (p i)) from funext fun i=>(X.U k (t i)).apply_symm_apply _]
   rfl
-- sector exact nonemptiness public Deck.Rigid.keeps. Nest drops. track aligned to *same* Trace.
abbrev FamilyBasis (S:Table C.book) := ∀ d:ℕ,change S d
structure Suspension (C:Family G) where
   p : Drop (Bel C.book)
   back d v : p d (adjStep (Maxwell.Free.scheme C.book.grid) d v)=v
   real d v : p d ((Bel C.book).conj (Maxwell.Free.spin_free C.labels) _ v)=(Bel C.book).conj (Maxwell.Free.spin_free C.labels) _ (p d v)
   axis d (s:Ortho) v : p d ((Maxwell.Free.gear C.book.grid).act _ s v)=(Maxwell.Free.gear C.book.grid).act _ s (p d v)
 theorem suspension_spared (C:Family G) : Nonempty (Suspension C) := by
    choose P hP hs hr using (Contacts.Rigid.keeps (R:=Maxwell.Free.gear C.labels) (Maxwell.Free.hierarchy C.labels) (Maxwell.Free.gear_laws C.labels) (Maxwell.Free.phase_orientation C.labels) (Maxwell.Free.scheme_filters C.labels))
    exact ⟨⟨P,hP,hr,hs⟩⟩

variable (R : Suspension C)
include h R in
lemma align_lift (Y:ℕ→FamilyBasis (C:=C) S)(hY:Approaches (path X) (fun i d=>(Y i d).toLinearMap))(hA:∀ d:ℕ, ∀ᶠ i in atTop,AlignO F.sector (H₁).spin H _ (Y i d)):
    ∃ X':Scaling S,X'.r=X.r ∧ Approaches (path X') (isoPanel X') ∧ Stable (H₁).spin H.spin W₁ W₀ X' ∧ (∀ d:ℕ, ∀ᶠ i in atTop,AlignO F.sector (H₁).spin H _ (X'.U i d)) ∧ ∀ d≤4, ∀ᶠ i in atTop,X'.U i d=Y i d:=by
   let Q (i:ℕ):= corrected W₁ W₀ R.p (fun d=>(Y i d).toLinearMap)
   let hW:=F.phase.transport.injection; let hV:=(Maxwell.Free.scheme_filters C.labels); let hR:=F.phase.transport.rights; let hr:=(Maxwell.Free.phase_orientation C.labels)
   let Z4:=baseRights (C:=C) (H:=H) h
   let ZS:=F.phase.transport.spots
   have hh d:∀ᶠ i in atTop, StraightAt (H₁).spin H.spin (fun d=>(Y i d).toLinearMap) d:= (hA d).mono fun i hi=>
      ⟨hi.real, fun s x=> by change Y i d ((Bel C.book).mirror _ _ _ x)= _; rw[← Z4.signed,hi.axis, ZS.signed]; rfl⟩
   have hh'(d):∀ᶠ i in atTop,StraightAt (H₁).spin H.spin (Q i) d:= solid (H:=H₁) (a:=H) _ hR hr R.p R.real (fun d s x=>by rw [← Z4.signed, R.axis, Z4.signed]) hh d
   have ha : Approaches (path X) Q:= adjusts H₁ H hW hV (path X) R.p hY
   have he d : ∀ᶠ k in atTop,Bijective (Q k d):= by
      filter_upwards[MeterTest.injects (H₁).smooth H ha d] with k hk; exact ⟨hk,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (X.U k d).finrank_eq).1 hk⟩
   let M k d:=if h:Bijective (Q k d) then LinearEquiv.ofBijective _ h else X.U k d
   let X' : Scaling S:= ⟨M,X.xi,X.r,X.sign,X.positive,X.later,X.drips⟩
   have hB(d):∀ᶠ i in atTop, isoPanel X' i d=Q i d := by filter_upwards[he d] with k hk; unfold X' isoPanel M; dsimp only; rw[dif_pos hk]; rfl
   have hz d e (i:ℕ) (h:d ≤ e) (x): Q i e ((W₀).rise h x)= (W₁).rise h (Q i d x) := balanced H₁ H _ hW hV R.p R.back _ _ _ _
   have hUnit(d) : ∀ᶠ i in atTop,Q i d ((B).unit d)= S.unit d :=by
       filter_upwards[hA 0] with k hk
       rw[← (W₀).fixs hV H.laws (Nat.zero_le d), hz,show Q k 0 ((B).unit 0) = S.unit 0 from hk.unit,(W₁).fixs hW (H₁).laws]
   have hS : Stable (H₁).spin H.spin W₁ W₀ X':=by
      refine ⟨fun d=> ?_, fun d e h=> ?_,fun d=>?_⟩
      · filter_upwards [hh' d,hB d] with k hk ht
        constructor
        · intro v x; change isoPanel X' k d _=S.mirror _ _ _ (isoPanel X' k d _); rw [ht]; exact hk.reflects ..
        intro x;change isoPanel X' k d _=S.conj _ _ (isoPanel X' k d _);rw [ht];exact hk.bars ..
      · filter_upwards [hB d,hB e] with i hi he v;change isoPanel X' i e _= (W₁).rise _ (isoPanel X' i d _); rw[hi,he,hz]
      filter_upwards [hB d,hUnit d] with i hi hP; change isoPanel X' i d _=_;rw[hi]; exact hP
   have hτ d:∀ᶠ i in atTop,∀ s x,Q i d ((τ).act d s x)=(τ₁).act d s (Q i d x):=by
       induction d with
       | zero => filter_upwards [hA 0] with i hi; exact hi.axis
       | succ d IH=>
           filter_upwards [IH,hA (d+1)] with i hi hL s x
           have hp (d x): (Y i d).toLinearMap x = Y i d x:=rfl
           have hu(x:(B).Field d): corrected W₁ W₀ R.p (fun d=>(Y i d).toLinearMap) d ((τ).act d s x)=(τ₁).act d s (Q i d x):=hi s x
           unfold Q; rw [correction,correction, R.axis d s,hu]; simp_rw [hp]
           unfold adjStep; rw [← Z4.filtered d (d+1),← map_sub,hL.axis, map_add, ZS.filtered d (d+1)]
   refine ⟨X',rfl, ⟨fun n v=> ?_⟩,hS, fun d=> ?_,fun d he=> ?_⟩
   · refine (ha.values n v).congr (fun i=> (smoothZoom (H₁).smooth _ (X'.positive i)).sub (smoothDisc (T:=Bel C.book) H.smooth _)) ?_
     filter_upwards[eventually_all.mpr (fun i:Fin n=> hB (v i).1)] with k hk x _
     change Next.UVStress.tested _ _ _ _ - _ = Next.UVStress.tested _ _ _ _ - _
     unfold Next.UVStress.tested; rw [show (panels (Q k) ∘ v)=panels (isoPanel X' k) ∘ v from funext (fun i=> by unfold panels Function.comp; dsimp only; rw [hk])]; rfl
   · filter_upwards [hS.hsym d,hB d,hS.units d,hτ d] with i hi ht hx hh
     refine ⟨hi.2,hx,fun s x=> ?_⟩; change isoPanel X' i d _=(τ₁).act _ _ (isoPanel X' i d _); rw [ht,hh]
   cases d with
   | zero=> filter_upwards [hB 0] with i hi; exact LinearEquiv.toLinearMap_injective hi
   | succ d =>
       filter_upwards [hB (d+1),hUnit d,hA (d+1)] with i hi hd hD
       apply LinearEquiv.toLinearMap_injective; change isoPanel X' i (d+1)=_; rw[hi]; apply LinearMap.ext; intro v
       unfold Q; rw [correction]
       obtain ⟨a,hx⟩:= UVNext.FreeStress.below C.book.grid h (d:=d) (by omega) (R.p d v)
       simp only [hx,map_sub,map_smul, LinearEquiv.coe_coe]; rw [show _=S.unit d from hd]; unfold adjStep; rw [(W₀).fixs hV H.laws, (W₁).fixs hW (H₁).laws,hD.unit]; abel

lemma angles {V:∀ i,Vane C i}(hs:Scribe f X V Z F.sector l H₁ H): ∃ X':Scaling S, X'.r=X.r ∧ Approaches (path X') (isoPanel X') ∧ Stable (H₁).spin H.spin W₁ W₀ X' ∧ (∀ d:ℕ, ∀ᶠ i in atTop,AlignO F.sector (H₁).spin H _ (X'.U i d)) ∧ ∀ᶠ i in atTop, AtAngle F (H:=H) (𝓛:=l) h (X'.r i) (X'.U i 4):=by
   obtain ⟨R⟩:= suspension_spared C
   obtain ⟨P,hP,hX⟩:= fulfill F h hs
   choose U hU hS using alignsO h hs
   let Y(d:ℕ)(k:ℕ):change S d:= update (fun d=> U d k) 4 (P k) d
   have b(d): Tendsto (fun k=> moveV (S:=S) d (X.U k d) (Y d k)) atTop (𝓝 1) ∧ ∀ᶠ i in atTop,AlignO F.sector (H₁).spin H _ (Y d i):=by
       unfold Y; by_cases he:d=4; swap; simp_rw [update_of_ne he]; exact ⟨hU d,hS d⟩
       rw [he]; simp_rw [update_self]; exact ⟨hP,hX.mono fun i hi=>hi.frame.align⟩
   obtain ⟨X',hh,hv,hR,hL,hW⟩:= align_lift F h R (fun k d=> Y d k) (flows F (fun k d=>Y d k) hs.monorail.approach (fun d=>(b d).1)) (fun d=>(b d).2)
   refine ⟨X',hh,hv,hR,hL,?_⟩
   filter_upwards[hW 4 le_rfl,latium F h hs P hP hX] with k hk hh'
   rw [hh,hk]; rw [show Y 4 k=P k from update_self ..]; exact hh'
end YM.Pier.Lair

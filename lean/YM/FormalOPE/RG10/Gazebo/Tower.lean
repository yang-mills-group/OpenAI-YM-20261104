import YM.FormalOPE.RG10.Gazebo.Dwell
/-! Equip the whole (not inverse pose yet) coherently: Lie subspace full rank on propagated
marks including any admissible test arity. At each horizon only finite choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Gazebo
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle
open RG10.Position RG10.Position.Grade Deck Shutters
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{d k n:ℕ} (h:d ≤ k)
local notation "𝒩" d=> tents F d
local notation "α"=>PertExtension.Physical.Profile.n
local notation "ℳ" d=> Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "𝒫"=> PertExtension.Physical.Profile
local notation "V" d => Questionnaire (J:=Deck F d) (arity:=PertExtension.Physical.Profile.n)
local notation "S"=>ascend α (climb F h)
namespace Ticket
variable (T:Ticket F d) (U:Ticket F k)

def Span := ∀ p : (ℳ k)→ℝ, ρ h (U.beamtest p)= T.beamtest (p∘S)
def housed (s:Finset 𝒫)(J:Ticket F k): Prop:= s⊆J.tests
private abbrev bow (B:𝒩 k):= B-σ h (ρ h B)
private def column (I J:Type*)(f:I→J) : (J→ℝ) →ₗ[ℝ] (I→ℝ) where
 toFun a:=a ∘ f
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
local notation "R"=> T.tests∪U.tests
private def house := column ((V d) T.tests) ((V k) R) (fun q=>⟨⟨q.1.1, mem_union_left _ q.1.2⟩,climb F h ∘ q.2⟩)
private def building := column ((V k) U.tests) ((V k) R) (fun q=>⟨⟨q.1.1, mem_union_right _ q.1.2⟩,q.2⟩)

private def ensemble : Ticket F k:= ⟨R, σ h ∘ₗ T.receive ∘ₗ house h T U+(LinearMap.id-σ h ∘ₗ ρ h) ∘ₗ U.receive ∘ₗ building T U⟩
lemma view (p : (ℳ k)→ℝ) : (ensemble h T U).beamtest p= (σ h (T.beamtest (p∘ S))) + bow h (U.beamtest p):= rfl
lemma span (p : (ℳ k)→ℝ) : ρ h ((ensemble h T U).beamtest p)= T.beamtest (p∘ S):= by rw [view,map_add,bow,map_sub,marches,marches,sub_self,add_zero]
lemma starred (ht:T.Perfect)(hu:U.Perfect) : (ensemble h T U).Perfect := by
 intro i; rw [view,hu,clip_beam,ht]; unfold bow; abel
lemma day (ht:T.Paired)(hu:U.Paired) : (ensemble h T U).Paired := by
 intro p; rw [view,view,hu,show (glow α (Deck.slots F k) p ∘ S)= glow α (Deck.slots F d) (p ∘ S) from rfl,ht]; unfold bow; rw [map_add,map_sub,catch_rising,catch_rising,catch_falling]

theorem linking (ht:Span h T U) : Bindings α (climb F h) T.set U.set:= by
 constructor
 · ext i j : 2; simp [Ticket.set, Physical.diag,clip,(Deck.climb_inj F h).eq_iff]
 · exact fun _ h=> transfers _ h
 · intro i j hj; exact if_neg (fun x=> hj ⟨i,x⟩)
 · exact fun i hi=> no_pass h ((votes _).mp ((pinned i).1 hi).1).1
 · intro p; exact congr_arg Subtype.val (ht p)
 have he:= ht (raw F k); rw [show raw F k ∘ S= _ from (Plan.fresh_clips (F:=F) h).symm] at he; exact congr_arg Subtype.val he

lemma Span.refl : Span (le_refl d) T T := fun _=> by
 rw [show climb F (le_refl d)=id from funext fun i=>rfl]; rfl
lemma chain_grade (hd:d≤k) (hk:k≤n) (i : Deck F d) : climb F hk (climb F hd i)=climb F (le_trans hd hk) i:= rfl
lemma Span.together (ht:Span h T U) {hk:k≤n}{E : Ticket F n}(he:Span hk U E) : Span (le_trans h hk) T E:= by
 intro i; rw [← show ascend α (climb F hk) ∘ S= ascend α (climb F (le_trans h hk)) from rfl]; change ρ h (ρ hk (E.beamtest i))=T.beamtest ((i ∘ _) ∘ S); rw [he,ht]

abbrev quality := T.Perfect ∧ T.Paired
-- Per-horizon stabilization but compatible choices regardless.
variable (P:Plan F)
include P in
lemma stabilize : ∃ H: (k:ℕ)→ Ticket F k, (∀ d,(∀ b≤d,Pert.Position.Frozen F b)→(H d).quality) ∧ ∀ a b (h:a≤b), Span h (H a) (H b):= by
 -- Use junk zero components anywhere beyond the available individual ranks if needed (not an Official then).
 let w : ℕ→Prop:= fun i=> Pert.Position.Frozen F i
 have h (a:ℕ): ∃ Z:Ticket F a, w a→Z.quality:= by by_cases h:w a; obtain ⟨v,h⟩:= lit P h; exact ⟨v,fun _=>h⟩; exact ⟨⟨∅,0⟩,fun hu=>(h hu).elim⟩
 choose M hm using h
 let T (x:ℕ):Ticket F x:= Nat.rec (motive:=fun x=>Ticket F x) (M 0) (fun n IH=> ensemble (Nat.le_succ n) IH (M (n+1))) x
 have H k: T (k+1)=ensemble (Nat.le_succ k) (T k) (M (k+1)):=rfl
 refine ⟨T, ?_,?_⟩
 · intro d hu; induction d with
   | zero=> exact hm 0 (hu _ (le_refl _))
   | succ d IH=> obtain ⟨hx,hy⟩:=IH (fun i he=>hu i (le_trans he (Nat.le_succ _))); obtain ⟨hb,hc⟩:= hm _ (hu _ (le_refl _)); exact ⟨starred _ _ _ hx hb,day _ _ _ hy hc⟩
 intro a b hab; induction b,hab using Nat.le_induction with
 | base=>exact Span.refl (T a)
 | succ k ha IH=>rw [H]; exact Span.together _ _ (T k) IH (span _ _ _)

end Ticket

variable (P:Plan F)
-- choose the stock on the continuum free horizon. Wire this independently chosen prescription
-- into RG06/08/09/11 then projection conversions/etc.
def rok (d:ℕ): Ticket F d := (Ticket.stabilize P).choose d
def porter : Stock F:= fun d=> (rok P d).set
lemma porter_low (hg:G.Simple) (d:ℕ)(hd:d≤4) :
  (porter P d).Regular (Physical.free (L:=Maxwell.standard F) (deck F d)) ∧ Blinds (Deck.slots F d) (porter P d) := by
 obtain ⟨he,hv⟩: (rok P d).quality:= (Ticket.stabilize P).choose_spec.1 d (fun b hb=> (lt_or_eq_of_le (hb.trans hd)).elim (fun h=> Pert.Rigid.first_frozen F hg h) (fun h=>h.symm ▸ Pert.Rigid.frozen_four F hg)); exact ⟨(rok P d).rank_free he,(rok P d).lights P hv⟩
lemma transporter : Bindings (PertExtension.Physical.Profile.n) (climb F h) (porter P d) (porter P k):= Ticket.linking _ _ _ ((Ticket.stabilize P).choose_spec.2 d k h)

-- The full needed supply
structure Hall (F:Frames G) : Prop where
 rank : ∀ d,Pert.Position.Frozen F d

theorem welcome (u:Hall F) : Official (porter P) ∧ Lantern (porter P) := by
 have he (d) : (rok P d).quality:= (Ticket.stabilize P).choose_spec.1 d (fun b _=>u.rank b)
 exact ⟨⟨fun _=>rfl,fun d _=>pinned (F:=F) (d:=d) _, fun d=>Ticket.rank_free _ (he d).1, fun _ _ h=>transporter h P⟩,fun d=> Ticket.lights _ P (he d).2⟩
end YM.FormalOPE.RG10.Gazebo

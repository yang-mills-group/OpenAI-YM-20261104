import YM.Contacts.Tempo.Pendulum
namespace YM.Contacts.Tempo
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
open Harrier Harrier.Transfer Parcel Planned.PrimaryIntegral295
open Cartons Tensor Place Carrier MultiNext.SignedSource Pattern Barrage Barrage.Reserve.Oasis Analysis
variable {A: Ink G h M} {S:Boom} {e:Parcel G}{s:Parcel.Step}{K j':ℕ}
namespace Grounds
variable (T:Grounds A e S s K k D ζ) {x:Dye G}
local notation "Γ" => terrain ζ (Dye G)
local notation "Η" => terrain (2*ζ) (Dye G)
local notation "η" => bath ζ k (Dye G)
local notation "τ" => hop e s M h
local notation "R" => play h M e s
variable {V:Badge A.prism→Sketch G}
local notation "Ζ" => (2*ζ:ℝ≥0)
abbrev ground (A:Ink G h M):= Finset.univ.filter (fun v:Badge A.prism=> v.win<h)
abbrev layer (A:Ink G h M)(k d:ℕ) := Finset.univ.filter (fun v:Badge A.prism=> v.slot=k ∧ v.win=d)
structure Prospect (A:Ink G h M)(D:ℕ)(x:Dye G)(ζ:ℝ≥0)(V:Badge A.prism→Sketch G):Prop where
   home (v):Living x M D (V v) ζ
   thin (v j) (he:v.slot<j) (p:Cards): V v p 0 j=0
   push (v u: Badge A.prism)(he:v.slot=u.slot)(h:u.win≤ v.win): u.key (V v) M 0=if u=v then 1 else 0
namespace Prospect
variable (hc:Prospect A D x (2*ζ) V)
include T
lemma purse_ok (x:Dye G):Prospect A D x (2*ζ) A.purse:=⟨fun u=> A.life u T.center, fun u j h p=> (show u.read p • A.mask u.loc 0 j=0 from (by rw [(A.paint _).rank 0 j (by change _ ≠ u.slot+0; omega),smul_zero])), fun u v _ _=> by rw [A.character x]; simp only [true_and]; simp only [eq_comm (a:=u)]⟩
include hc
-- T primed for its light and relation
lemma blink (u v:Badge A.prism)(he:u.slot=v.slot)(hx:u.win ≤ v.win): u.key (surge (V v) i) M i= if u=v then 1 else 0:= by
   unfold Badge.key surge; rw [fill_shift _ ((hc.home v).lineage u.phi) T.ready,if_pos le_rfl,Nat.sub_self]; exact hc.push v u he.symm hx
omit T
lemma past_blank {u:Badge A.prism}(he:u.slot≤ r) : Harrier.Before η D x (surge (V u) i) i r 0:= by
    intro j l hj; rw [Enroll, show sail (surge _ i) j l=0 from (show sail (surge (V u) i) j l=0 from ?_)]; exact w_zero
    funext φ; rcases hj with h|⟨h,h'⟩; · unfold Harrier.sail surge shiftA; rw [if_neg (by omega)]; rfl
    subst j; unfold Harrier.sail surge shiftA; rw [if_pos le_rfl,Nat.sub_self]; exact hc.thin u l (by omega) _
end Prospect
abbrev Merit (A: Ink G h M):= Badge A.prism→ℝ
abbrev Grant (A: Ink G h M):= Badge A.prism→ℕ→ℝ
def Edited (A:Ink G h M)(V:Badge A.prism→Sketch G)(K:ℕ)(c:Grant A): Sketch G :=∑ v∈ground A,∑ i∈Finset.Iic K, (c v i) • surge (V v) i
def Held (A:Ink G h M)(V:Badge A.prism→Sketch G)(K:ℕ)(y: Sketch G):Prop:= ∃ c:Grant A,y=Edited A V K c
def beat (A:Ink G h M)(V:Badge A.prism→Sketch G)(i r w:ℕ)(t:Merit A): Sketch G := ∑ v∈layer A r w, t v • surge (V v) i
lemma Edited.plus {f g:Grant A}: Edited A V K (f+g)=Edited A V K f+Edited A V K g:= by simp only [Edited,Pi.add_apply,add_smul,Finset.sum_add_distrib]
lemma Edited.minus {f g:Grant A}: Edited A V K (f-g)=Edited A V K f-Edited A V K g:= by simp only [Edited,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]
lemma Held.free : Held A V K 0:= ⟨0,(by unfold Edited; simp)⟩
lemma Held.plus {F U:Sketch G} (h:Held A V K F)(he:Held A V K U):Held A V K (F+U):= by obtain ⟨f,rfl⟩:=h; obtain ⟨p,rfl⟩:=he; exact ⟨f+p,Edited.plus.symm⟩
namespace Prospect
variable (H:Prospect A D x (2*ζ) V) {f:Grant A}(t:Merit A)
include H
lemma financed (h:Held A V K P): Living x M D P (2*ζ):= by obtain ⟨g,rfl⟩:= h; exact Living.sum _ fun w _=> Living.sum _ (fun i _=> ((H.home w).surgeM _).scale _)
lemma beats_health : Living x M D (beat A V i r n t) (2*ζ):= Living.sum _ fun v _=> ((H.home v).surgeM i).scale _
omit H in
lemma beat_paid (hi:i≤K)(hn:n<h) : Held A V K (beat A V i r n t):= by
    let α:=Grounds.layer A r n; let β:= ground A; let y (p:Badge A.prism)(j:ℕ):= if p∈α ∧ i=j then t p else 0; let f(p):=∑ j∈Finset.Iic K,y p j • surge (V p) j; have he:α⊆β:= fun _ hx=>mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2.2.trans_lt hn⟩; refine ⟨y,?_⟩; change _=∑ p∈β,f p; rw [← Finset.sum_subset he (f:=f) (fun p _ hp=> Finset.sum_eq_zero fun i _=> by rw [show y p i=0 from if_neg (fun h=>hp h.1),zero_smul])]; apply Finset.sum_congr rfl; intro v hv; unfold f; rw [Finset.sum_eq_single i]; rotate_left; · intro k hk hx; rw [show y v k=0 from if_neg (fun h=>hx h.2.symm),zero_smul]
    · simp only [Finset.mem_Iic,hi,not_true_eq_false,false_implies]
    rw [show y v i=t v from if_pos ⟨hv,rfl⟩]
lemma volume_mute : Harrier.Before η D x (beat A V i r n t) i r 0:= by refine (before_sum (b:=fun _=>0) (layer A r n) (P:=fun v=>t v • surge (V v) i) (?_ )).mon (by simp only [Finset.sum_const_zero,le_refl]); intro v hv; exact mul_zero ‖t v‖ ▸ before_scale _ (H.past_blank (mem_filter.mp hv).2.1.le)
include T
lemma aural (v:Badge A.prism)(hx:v.win≤n)(he:v.slot=r): v.key (beat A V i r n t) M i= if v.win=n then t v else 0:= by
   unfold beat; rw [v.key_many T.ready (layer A r n) (fun v _=> ((H.home v).surgeM _).scale _)]; let Z:=layer A r n; have h (u:Badge A.prism)(hp:u∈Z)(hy:u≠v): v.key (t u • surge (V u) i) M i=0:= by rw [v.key_scale ((H.home u).surgeM _) T.ready,Prospect.blink T H _ _ ?_ ?_,if_neg (Ne.symm hy),mul_zero]; exacts [he.trans (mem_filter.mp hp).2.1.symm,hx.trans_eq (mem_filter.mp hp).2.2.symm]
   by_cases hy : v.win=n; · rw [if_pos hy,Finset.sum_eq_single v, v.key_scale ((H.home v).surgeM _) T.ready, Prospect.blink T H v v rfl le_rfl,if_pos rfl,mul_one]; exact h; intro hi; exact (hi (mem_filter.mpr ⟨mem_univ _,he,hy⟩)).elim
   rw [if_neg hy]; exact Finset.sum_eq_zero fun u hu=> h u hu (fun hx=> hy ( (congr_arg Badge.win hx.symm).trans (mem_filter.mp hu).2.2))
end Prospect
end Grounds
end
end YM.Contacts.Tempo

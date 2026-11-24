import YM.Contacts.Procession.Ladder
/-! # Coupling a top Mark register; opacity cost & translation at every partial lift -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Xenon
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration
open Milling Milling.Steam Milling.Forge Pulse.Form
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {α β ι T : Type}{g:Gauge}{σ:ℝ≥0}{b:ℝ}{m:Side}{u h i k:ℕ} [AddCommGroup T]
abbrev Boys (i:ℕ)(X:Type) := Fin i→ X
abbrev Live (T α:Type) := T× Option α
def core (T α:Type) : T×α ↪ Live T α:=⟨fun q=>(q.1,some q.2), fun _ _ h=> Prod.ext (congr_arg (fun i:Live T α=> i.1) h) (Option.some.inj (congr_arg Prod.snd h))⟩
@[simp] lemma core_apply (T α:Type) (i:T)(a:α): core T α (i,a)=(i,some a):=rfl
def adder (x:T) (p:T×α) : T×α := (p.1+x,p.2)
def focus (x:T)(V:Boys i (T×α)) : Boys (i+1) (Live T α):= Fin.cons (x,none) (core T α ∘ adder x ∘ V)
def scroll (T α:Type)[AddCommGroup T] (i:ℕ): T×Boys i (T×α) ↪ Boys (i+1) (Live T α):= ⟨fun q=> focus q.1 q.2, fun ⟨x,a⟩ ⟨y,b⟩ H=> by
   have hh:focus x a=focus y b:= H; obtain rfl : x=y:= congr_arg Prod.fst (congr_fun hh 0); congr 1; refine funext fun i=>?_ ; have hx:adder x (a i)=adder x (b i):=(core _ _).injective (congr_fun H i.succ); exact Prod.ext (add_right_cancel (congr_arg Prod.fst hx)) ((show (a i).2=_ from (show (adder x (a i)).2=(adder x (b i)).2 from congr_arg (fun z:T×α=> z.2) hx)))⟩
def scarab (F:Field (Fin i) (T×α)) : Field (Fin (i+1)) (Live T α) := fun x=> if H:x∈Set.range (scroll T α i) then F H.choose.2 else 0
def stem (F:Field (Fin i) (T×α)):= printRun (scarab F)
lemma scar_read (F:Field (Fin i) (T×α))(x:T)(p):scarab F (focus x p)= F p:= by
   unfold scarab; split
   next h=> exact congr_arg F (congr_arg Prod.snd ((scroll T α i).injective h.choose_spec : h.choose = (x,p)))
   next h=> exact (h ⟨(x,p),rfl⟩).elim
lemma scar_species (i:ℕ)(u:Boys (i+1) (Live T α)) : u∈Set.range (scroll T α i) ↔ (u 0).2=none ∧ ∀ j:Fin i,(u j.succ).2≠none:= by
    constructor; · rintro ⟨v,rfl⟩; exact ⟨rfl,fun i=> nofun⟩ -- some.ne
    rintro ⟨hu,hf⟩; let a: T:= (u 0).1; choose v hv using fun j:Fin i=> Option.ne_none_iff_exists'.mp (hf j); refine ⟨(a,fun j=> ((u j.succ).1-a,v j)),funext fun j=> Fin.cases ?_ (fun j=>?_) j⟩; · exact Prod.ext rfl hu.symm
    exact Prod.ext (sub_add_cancel ..) (hv j).symm
lemma scar_shift (F:Field (Fin i) (T×α))(x:T)(p:Boys (i+1) (Live T α)): scarab F (adder x ∘p)=scarab F p:= by
   by_cases hx : p∈Set.range (scroll T α i)
   · obtain ⟨⟨z,p⟩,rfl⟩:=hx; change scarab F (adder x ∘ focus z p)=scarab F (focus z p); rw [show _=focus (z+x) p from (show adder x ∘ focus z p=_ from funext (fun i=> Fin.cases (show adder x (focus z p 0)=_ from rfl) (fun j=> Prod.ext (add_assoc ..) rfl) i)),scar_read,scar_read]
   unfold scarab; rw [dif_neg hx,dif_neg]; rw [scar_species] at hx ⊢; exact hx
variable {F:Field (Fin i) (Node α)}
-- counting cost by root and then by inverse orbit ray at all other choices of anchor
lemma playBill (p: Boys i (Node α))(x:Cover)(a:α): (terrain σ _).bill (focus x p)= fee (terrain σ α) (0,a) p:= by
    rw [fee_basis]; let v:= Fin.cons (α:=fun _:Fin (i+1)=>Node α) (0,a) p; have hp (j:Fin (i+1)): (focus x p j).1=(v j).1+x:= by
       refine Fin.cases ?_ (fun j=>?_) j; · change x=0+x; rw [zero_add]
       rfl
    have ht j k:(terrain σ _).fee (focus x p j) (focus x p k)=(terrain σ _).fee (v j) (v k):= NNReal.eq (by exact congr_arg (fun u:Cover=>Real.exp (σ*(size u:ℝ))) (show _=_ from (by rw [hp,hp,add_sub_add_right_eq_sub] : (focus x p k).1-(focus x p j).1=(v k).1-(v j).1))) -- simplify
    unfold Pulse.Range.bill Pulse.Range.height; simp_rw [ht]; rfl
lemma scar_paid (a:α)(h:Rest (terrain σ α) (0,a) F b) : Rooted (terrain σ _) (scarab F) b:= by
    let A:=scroll Cover α i; refine ⟨h.cash,fun j x=>?_ ⟩; let M(y: Locked (Live Cover α) j x):=‖scarab F y.val‖*(terrain σ _).bill y.val; let P(y:Locked (Live Cover α) j x): Prop:= y.val∈Set.range A; let Q(y:Subtype P):= (y.property: y.val.val∈Set.range A).choose; let N(y:Subtype P):= (Q y).2; have he(y:Subtype P): y.val.val=focus (Q y).1 (N y):= (show y.val.val=A (Q y) from y.2.choose_spec.symm)
    have hf: Injective N:= by
       intro y z h; have hh(y:Subtype P) : focus (Q y).1 (N y) j=x:= by rw [← he]; exact y.val.property
       apply Subtype.ext; apply Subtype.ext; rw [he,he,h]; apply congr_arg (fun x=> focus x (N z)); have H:= congr_arg Prod.fst ((show focus (Q y).1 (N z) j= x from h ▸ hh y).trans (hh z).symm); generalize hJ:j=q at H; obtain rfl|⟨j,rfl⟩:= Fin.eq_zero_or_eq_succ q; exact H; exact add_left_cancel H
    let t(y:Boys i _):=‖F y‖* fee (terrain σ α) (0,a) y; have hv:SumBudget (M∘ Subtype.val (p:=P)) b:= budget_map h N hf (fun y=> by change M y.val=t (N y); unfold M t; rw [he,scar_read, playBill _ _ a]); let w(y) (he:¬ P y): M y=0 := by unfold M; rw [scarab,dif_neg he,norm_zero,zero_mul]
    constructor; · exact fun _=> by positivity
    have Hs: HasSum M (∑' y:Subtype P,M y.val):= (Subtype.val_injective.hasSum_iff (fun i hi=>w i (fun h=> hi ⟨⟨i,h⟩,rfl⟩))).1 hv.2.1.hasSum; exact ⟨Hs.summable,Hs.tsum_eq.le.trans hv.2.2⟩
end YM.Contacts.Procession.Xenon

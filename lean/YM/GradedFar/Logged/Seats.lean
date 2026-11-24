import YM.GradedFar.Logged.Full
/-! Move the accounting to the through-cap operands from those same tokens. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Seats
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log
open Tree Tree.Node
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
  {I J:Type} [Fintype I] [Fintype J] {P:Prescription F.sector.derivatives}
local notation "nearSet"=>Tree.near I J
local notation "outerSet"=>Tree.outer I J
local notation "tree"=>Tree.frame I J
local notation "X"=> Tree.position
local notation "bare"=> Stage.bare
-- robust equiv crossing (raw construction uses arbitrary enumerate of I,J)
def named (u:I→C.book.Token)(v:J→C.book.Token) : Node I J→ C.book.Token
| leaf i=> u i| far j=>v j| base| child=> C.book.one 0
abbrev wholeCost (T:Table C.book) (r : Viewers F):=T

def core (i:I) : ↥nearSet:= ⟨leaf i,near_mem i⟩
def horizon (q:I⊕J) : ↥(tree).leaves :=match q with
| .inl i=> ⟨leaf i,(by rw [Tree.leaves]; exact mem_union_left _ (near_mem i))⟩
| .inr j=> ⟨far j,(by rw [Tree.leaves]; exact mem_union_right _ (terminal_mem j))⟩
def turn (q:Unit⊕J) : ↥outerSet :=match q with
| .inl _=>⟨child,mem_insert_self ..⟩
| .inr j=>⟨far j,mem_insert_of_mem (terminal_mem j)⟩
lemma core_alive:Bijective (core (I:=I) (J:=J)):= ⟨fun _ _ h=>Node.leaf.inj (congrArg Subtype.val h), fun i=> by obtain ⟨i',hi⟩:= Tree.names i; exact ⟨i',Subtype.ext hi.symm⟩⟩
lemma horizon_fit:Bijective (horizon (I:=I) (J:=J)):= by
    constructor
    · rintro (i|j) (k|l) hx <;> replace hx:= congrArg Subtype.val hx <;> unfold horizon at hx <;> simp at hx <;> simp [hx]
    rintro ⟨q,h⟩; have hp:=h; rw [Tree.leaves] at hp; rcases Finset.mem_union.mp hp with h|h
    · obtain ⟨i,hi⟩:= Tree.names (⟨q,h⟩:↥nearSet); exact ⟨.inl i, Subtype.ext hi.symm⟩
    obtain ⟨j,hj⟩:=Tree.names_far h; exact ⟨.inr j,Subtype.ext hj.symm⟩
lemma turn_fit : Bijective (turn (I:=I) (J:=J)):= by
    constructor
    · rintro (⟨⟩|j) (⟨⟩|l) hx <;> replace hx:= congrArg Subtype.val hx <;> unfold turn at hx <;> simp at hx <;> simp [hx]
    rintro ⟨q,h⟩; rcases Finset.mem_insert.mp h with q|hq
    · exact ⟨.inl (), Subtype.ext q.symm⟩ -- q shadow
    obtain ⟨i,hi⟩:=Tree.names_far hq; exact ⟨.inr i, Subtype.ext hi.symm⟩
private lemma exchange {α β:Type}[Fintype α][Fintype β] (f : α→ β)(h:Bijective f){x':β→E4}{v':β→ C.book.Token}
    (x:α→E4)(v:α→C.book.Token)(hp: x= x'∘ f)(hv: v=v'∘ f): Injective x ↔ Injective x':= by
    rw [hp]; constructor; · intro ht u v hx; obtain ⟨u,rfl⟩:= h.2 u; obtain ⟨v,rfl⟩:= h.2 v; exact congrArg f (ht hx)
    intro h'; exact h'.comp h.1
lemma exchange_read {α β:Type}[Fintype α][Fintype β] (f : α→ β)(h:Bijective f){x':β→E4}{v':β→ C.book.Token}
    (x:α→E4)(v:α→C.book.Token)(hp: x= x'∘ f)(hv: v=v'∘ f)(hx:Injective x)(s:Viewers F): observe (spectator F s) x v = observe (spectator F s) x' v' := by
    have ht:=(exchange f h x v hp hv).mp hx; rw [hp,hv]; exact perm_observe (spectator F s) (spectate F s).laws.toSymmetric (Equiv.ofBijective _ h) _ ht
lemma observe_bare {α:Type}[Fintype α](x:α→E4)(v:α→C.book.Token)(s:Viewers F)(hx:Injective x) :
    observe (spectator F s) (beside x (bare:Fin 0→E4)) (beside v (bare:Fin 0→ C.book.Token))=observe (spectator F s) x v:= by
    apply Eq.symm (exchange_read F Sum.inl ⟨Sum.inl_injective,fun i=>?_⟩ x v rfl rfl hx s); rcases i with i|i; exact ⟨i,rfl⟩; exact Fin.elim0 i
lemma tree_skin (p : I→ C.book.Token) (x:I→E4) {x':↥nearSet→ E4}{p':↥nearSet→C.book.Token}
    (hp : p=p'∘ core)(hx:x=x'∘core) (o:E4) (a : Mode F.sector.derivatives): P.ope a x p o=P.ope a x' p' o := by
    unfold Prescription.ope; refine Finset.sum_congr rfl fun s hs=> ?_; apply congrArg (_*·); unfold Prescription.reading
    let v : (I ⊕ Fin s.n) ≃ (↥nearSet ⊕ Fin s.n):= Equiv.sumCongr (Equiv.ofBijective _ core_alive) (Equiv.refl _)
    let z:=beside (fun i=>x i-o) (bearing s); let y:=beside (fun i=>x' i-o) (bearing s)
    have hi:z=y∘v := by funext i; cases i with | inl i=> exact congrArg (·-o) (congrFun hx i) | inr i=> rfl
    have hl:beside p s.letter=(beside p' s.letter)∘v:=by funext i; cases i; exact congrFun hp _; rfl
    have h:= exchange _ v.bijective _ _ hi hl
    change (if Injective z then observe S z _ else 0)=(if Injective y then observe S y _ else 0)
    by_cases ht:Injective z; · rw [if_pos ht,if_pos (h.mp ht)]; exact exchange_read F _ v.bijective _ _ hi hl ht none
    rw [if_neg ht,if_neg (fun he=> ht (h.mpr he))]

abbrev homing (r:ℝ)(o:E4)(x:I→E4) := fun i=>o+r • x i
variable (x:I→E4)(y:J→E4)(o:E4)(r t:ℝ)(p:I→C.book.Token)(q:J→C.book.Token)(s:Viewers F)
local notation "a'"=>Arboreal
local notation "ψ"=>Tree.position r t x y o
lemma demand (hp:Injective (beside (homing r o x) (homing t o y))) : Full.demand F s ψ (tree).leaves (named p q) = observe (spectator F s) (beside (homing r o x) (homing t o y)) (beside p q) := by
    have he : beside (homing r o x) (homing t o y)=(crop ψ (tree).leaves)∘ horizon:=by funext i; rcases i with i|i<;> rfl
    have hv : beside p q=(crop (named p q) (tree).leaves)∘ horizon:=by funext i; rcases i with i|i<;> rfl
    unfold Full.demand Arboreal.whole
    rw [observe_bare F _ _ s ((exchange _ horizon_fit _ _ he hv).mp hp)]; exact (exchange_read F _ horizon_fit _ _ he hv hp s).symm
local notation "fs"=>tree
lemma old_read (hv:Injective (beside (sole o) (homing t o y)))(h:ℕ):
    (∑ u ∈ bands F.sector.derivatives h, coalesce P nearSet ψ (named p q) child u * Full.demand F s ψ outerSet (update (named p q) child (P.letter u)))=
      P.truncated (spectator F s) h (homing r o x) p o (homing t o y) q:= by
    refine Finset.sum_congr rfl fun u hu=> ?_; unfold Prescription.termRead
    rw [tree_skin F p (homing r o x) (x':=crop ψ nearSet) (p':=crop (named p q) nearSet) rfl rfl o u]; unfold Full.demand Arboreal.whole; apply congrArg (fun z=> coalesce P nearSet ψ (named p q) child u*z)
    let v:= update (named p q) child (P.letter u)
    have hp:beside (sole o) (homing t o y)=(crop ψ outerSet) ∘ turn:=by funext i; rcases i with ⟨⟩|i<;>rfl
    have hq:beside (sole (P.letter u)) q =(crop v outerSet)∘ turn := by funext i; rcases i with ⟨⟩|i <;> simp [crop,v,Function.comp_apply,turn,named]; rfl
    rw [observe_bare F _ _ s ((exchange _ turn_fit _ _ hp hq).1 hv)]; exact (exchange_read F _ turn_fit _ _ hp hq hv s).symm
end YM.OPE.Logged.Seats

import YM.FVA2.Facade.Rift
/-!
 # Root-truss at the collapse. No assumption on fixed point interactions

 `Wire` exactly those interior fast-tree edges. At concatenation the rank of
 planted vertices agrees with rank at coarser and every added vertex strictly
 above that. Allows even parallel edges or self loops in the already mature graph.
 No identification here with a Landau gauge on all vertices (see `FVA2.Orbit`
 for terminal comparisons in linear gauges on the assembled fine field).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Facade
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb
open scoped Classical Topology BigOperators
variable {G: Gauge} {c f n:Side} {L:Fabric G c}
section limbs
variable {S:StepData c f}{H:S.patch.Branches S.kernel G}{hf:Even f.val}{t:S.Choices}
variable (P:Inside S.ratio)(T:(rift L).Truss)
local notation "Γ" => layer S H t hf L
local notation "D" => rift (Γ)
local notation "F" => embed_next (H:=H) (hf:=hf) (t:=t) (L:=L) S
local notation "V"=> Hub Γ

-- total ancestry beyond `L`'s vertices
private def summit : ℕ:= ∑ x: Hub L,T.height x
private def height0 (i: Hub Γ): ℕ:= Option.elim i (T.height none) (fun x=> match x with
                                                           | Sum.inl i => (summit T+1)+P.height i.val
                                                           | Sum.inr i=> T.height (some i))
private lemma flight (i: Hub L) : height0 P T (F i)= T.height i:= by cases i <;> rfl
private def branchUp (i:Hub Γ)(h:i≠none): Hub Γ:= match i with
                                          | none => False.elim (h rfl)
                                          | some (.inl i)=> hub Γ (P.up i.val i.property)
                                          | some (.inr i)=> F (T.parent (some i) (Option.some_ne_none _))
private def wireUp (i:Hub Γ)(h:i≠none) : Used Γ:= match i with
                                           | none=> False.elim (h rfl)
                                           | some (.inl i)=> Sum.inl (P.wire i.val i.property)
                                           | some (.inr i)=> Sum.inr (T.wire (some i) (Option.some_ne_none _))

lemma interior_up (i:Interior S) : hub Γ i.val=some (Sum.inl i):= by unfold hub; rw [dif_neg i.property]; rfl

private lemma onward (i:Hub Γ)(h:i≠none) : let j:=wireUp P T i h; let v:=branchUp P T i h; ((D).fromEdge j=v∧ (D).toEdge j=i) ∨ ((D).fromEdge j=i ∧ (D).toEdge j=v):= by
 dsimp only
 rcases i with _|i; exact (h rfl).elim; change Interior _⊕Quick L at i; cases i with
 | inl i=>
    obtain hor|hor:= P.orientation i.val i.property
    · exact Or.inl ⟨congr_arg (hub Γ) hor.1,(congr_arg (hub Γ) hor.2).trans (interior_up i)⟩
    exact Or.inr ⟨(congr_arg (hub Γ) hor.2).trans (interior_up i), congr_arg (hub Γ) hor.1⟩
 | inr i=>
    obtain hor|hor:= T.orientation (some i) (Option.some_ne_none _)
    · exact Or.inl ⟨congr_arg F hor.1, congr_arg F hor.2⟩
    exact Or.inr ⟨congr_arg F hor.1,congr_arg F hor.2⟩

 def spanH : (rift Γ).Truss where
 height:= height0 P T
 wire:= wireUp P T
 parent:=branchUp P T
 descend:= fun i h=> by
    rcases i with _|i; exact False.elim (h rfl); change Interior _⊕ Quick L at i; cases i with
    | inl i=>
        let y:= P.up i.val i.property
        change height0 P T (hub Γ y)< (summit T + 1) + P.height i.val; rw [hub]; split
        · rename_i hv; let v:= hub L (ancestral S.ratio y); change height0 P T (F v)<_; rw [flight]; have ha:T.height v ≤ summit T:= Finset.single_le_sum (f:=T.height) (fun _ _=> Nat.zero_le _) (Finset.mem_univ _); omega
        rename_i hv; exact Nat.add_lt_add_left (P.descend i.val i.property) _
    | inr i=>
       change height0 P T (F (T.parent (some i) (Option.some_ne_none _))) < T.height (some i); rw [flight]; exact T.descend (some i) _
 orientation:=onward P T

local notation "A"=> spanH P (H:=H) (t:=t) (hf:=hf) T
-- tree characterization. Used ≃ root⸺finer and deeper all.Verse.Loom
lemma sprig_now (i:OEdge f) : (A).Branch (Sum.inl i) ↔ P.Innate i:= by
 constructor
 · rintro ⟨v,h,hv⟩; rcases v with _|v; exact (h rfl).elim; change Interior _⊕ Quick L at v; cases v with
    | inl v=> exact ⟨v.val,v.property,Sum.inl.inj hv⟩
    | inr=> exact (Sum.inr_ne_inl hv).elim
 rintro ⟨v,hv,rfl⟩; exact ⟨some (Sum.inl (Subtype.mk v hv : Interior S)),(Option.some_ne_none _),rfl⟩
lemma sprig_later (i: Used L) : (A).Branch (Sum.inr i) ↔ T.Branch i:= by
 constructor
 · rintro ⟨v,h,hv⟩; rcases v with _|v; exact (h rfl).elim; change Interior _⊕ Quick L at v; cases v with
    | inl => exact (Sum.inl_ne_inr hv).elim
    | inr v=> exact ⟨some v,(Option.some_ne_none _),Sum.inr.inj hv⟩
 rintro ⟨v,h,hv⟩; rcases v with _|v; exact (h rfl).elim; exact ⟨some (Sum.inr v),(Option.some_ne_none _),congr_arg (Sum.inr (α:=OEdge f)) hv⟩
end limbs

 def fir {n: Side}{L:Fabric G n}(T:Cloth L) : (rift L).Truss:= match T with
 | .floor _ _ _=> { height:= fun _=>0, parent:= fun _ _=>none, wire:= fun i h => match i with
                                                                                      | none=> False.elim (h rfl)
                                                                                      | some i=> Empty.elim i,
                     orientation:=fun i h=> by cases i; exact False.elim (h rfl); next i=> exact Empty.elim i,
                     descend:=fun i h=>by cases i; exact False.elim (h rfl); next i=> exact Empty.elim i }
 | .inLayer P C=> spanH P (fir C)
-- emission of Bulk equivalence; `T` available, no decision field.
section
variable {S:StepData c f}{H:S.patch.Branches S.kernel G}{hf:Even f.val}{t:S.Choices}(P:Inside S.ratio) {C:Cloth L}
local notation "T0" => Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "Γ"=> layer S H t hf L
def graft : (Blocking.Index S P ⊕ (fir C).Bulk) ≃ (fir T0).Bulk where
 toFun x:= match x with
 | .inl x=> ⟨Sum.inl x.val,x.property ∘ (sprig_now P (fir C) x.val).mp⟩
 | .inr x=> ⟨Sum.inr x.val,x.property ∘ (sprig_later P (fir C) x.val).mp⟩
 invFun x:= match x with
 | ⟨.inl i,h⟩=> .inl (Subtype.mk i (fun hi=> h ((sprig_now P (fir C) i).mpr hi)))
 | ⟨.inr i,h⟩=> .inr ⟨i,h ∘ ((sprig_later P (fir C) i).mpr)⟩
 left_inv x:= by cases x<;> rfl
 right_inv x:= by cases x with | mk v h=> change OEdge f⊕ Used L at v; cases v<;> rfl
end
 def leeway {n:Side}{L: Fabric G n}(T:Cloth L) : Warm T ≃ (fir T).Bulk:= match T with
 | .floor _ _ _=> { toFun:= Empty.elim, invFun:= fun x=> x.val,
                     left_inv:=fun x=>Empty.elim x, right_inv:=fun i=> Empty.elim i.val }
 | .inLayer (S:=S) P C=> ((Equiv.refl (Blocking.Index S P)).sumCongr (leeway C)).trans (graft P)
end YM.FVA2.Facade

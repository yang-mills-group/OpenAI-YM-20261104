import YM.FormalOPE.RG10.BlockGauge.Rim
/-!
 # Chosen hierarchical diagram gauge graph

 genuine StepData sequence (block geometry included); torus only appears at quotient inversion.
 No curvature masks, no recovery of different period at step, all gauges share one vertex height.
 Choice is fixed with proof of independence on germ. Terminal slice still inversion quotient.
 This graph deliberately retains the bonds at which no further blocking done even when not used
 by insertions. They must stay for denominator.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Topology Function MeasureTheory PertExtension PertExtension.Orb Lattice RG
open InversionWard Push.Loops
open scoped Classical Topology ContDiff
-- indexed top. require even at every level (for integral independent inversion edge).
inductive Fabric (G:Gauge) : Side → Type
| endcap (n:Side) (h:_root_.Even n.val): Fabric G n
| layer {c f : Side} (S:StepData c f) (branch:S.patch.Branches S.kernel G) (choice:S.Choices) (h:_root_.Even f.val) (inner : Fabric G c) : Fabric G f
variable {G:Gauge} {c f n:Side}
namespace Fabric
variable (L : Fabric G n)
include L in
lemma even : _root_.Even n.val := by -- requires L
 cases L <;> assumption
-- Joint edges, Type; store top and tails. Every physical OEdge kept exactly once at each level.
-- write tails via recursive scheme so top Tree equivalence definal enough.
 def More {n} : Fabric G n → Type
 | .endcap _ _ => Empty
 | .layer (c:=c) _ _ _ _ L => OEdge c ⊕ More L
@[implicit_reducible] def iMore {n : Side} (L:Fabric G n) : Fintype L.More := by cases L with
                                    | endcap => unfold More; infer_instance
                                    | layer _ _ _ _ L => letI := iMore L; unfold More; infer_instance
termination_by structural L
attribute [instance] iMore
abbrev Path := OEdge n ⊕ L.More
-- Path.iCoarse in `.layer` tails. Ambient loom adjacency
 def otherFrom {n}(L:Fabric G n) : L.More→Vertex n:=
 match L with
 | .endcap _ _=>Empty.elim
 | .layer S _ _ _ L => (placement S.ratio) ∘ (Sum.elim (rim _).fromEdge (otherFrom L))
 def otherTo {n}(L:Fabric G n): L.More→Vertex n :=
 match L with
 | .endcap _ _=>Empty.elim
 | .layer S _ _ _ L=> placement S.ratio ∘ (Sum.elim (rim _).toEdge (otherTo L))

 def loom : Loom (Vertex n) L.Path where
 origin:=0
 fromEdge:=Sum.elim (rim _).fromEdge L.otherFrom
 toEdge:=Sum.elim (rim _).toEdge L.otherTo
lemma from_main (i: OEdge n):(L.loom.fromEdge (.inl i))=(rim n).fromEdge i:=rfl
lemma to_main (i: OEdge n):(L.loom.toEdge (.inl i))=(rim n).toEdge i:=rfl
variable (S:StepData c f)(H:S.patch.Branches S.kernel G)(t:S.Choices)(hf:_root_.Even f.val) (L' : Fabric G c)
local notation "Γ"=> (layer S H t hf L')
-- convenience
 def tailLink (i:L'.Path) : (Γ).Path:= Sum.inr (show (Γ).More from i)
@[simp] lemma from_tail (i : L'.Path): (Γ).loom.fromEdge (tailLink S H t hf L' i)= placement S.ratio (L'.loom.fromEdge i):= rfl
@[simp] lemma to_tail (i : L'.Path): (Γ).loom.toEdge (tailLink S H t hf L' i)= placement S.ratio (L'.loom.toEdge i):= rfl
-- preferred top truss for integrating or identifying top-only PE. More general choices later.
 def atop : L.loom.Truss where
 height:= (staple n).height
 parent:=(staple n).parent
 wire v h := .inl ((staple n).wire v h)
 descend _ _:= (staple n).descend _ _
 orientation _ _:=(staple n).orientation _ _
lemma atop_branch (i:OEdge n): L.atop.Branch (.inl i) ↔ Orb.Branch i:= by
 constructor
 · rintro ⟨v,hv,h⟩
   exact (same_staple i).mp ⟨v,hv,Sum.inl.inj h⟩
 intro h; obtain ⟨v,hv,rfl⟩:= (same_staple i).mpr h; exact ⟨v,hv,rfl⟩
lemma atop_not (i:L.More): ¬ L.atop.Branch (.inr i):= by rintro ⟨v,hv,h⟩; change Sum.inl _ = _ at h; simp at h; -- may fail parser
abbrev LinksOn:= L.Path → G.El
 def principal (u: LinksOn L): LinkFrame G n:=u∘Sum.inl
 def future (u: LinksOn Γ):= u ∘ tailLink S H t hf L'
@[simp] lemma spin_main (g:Vertex n→ G.El)(u:L.LinksOn) : L.principal (L.loom.spin g u) = even_spin (g ∘ track) (L.principal u):= spin_agrees _ _
@[simp] lemma spin_future (g:Vertex f→ G.El)(u:(Γ).LinksOn): future S H t hf L' ((Γ).loom.spin g u)= L'.loom.spin (g ∘ placement S.ratio) (future S H t hf L' u):= rfl
end Fabric
end YM.FormalOPE.RG10.BlockGauge

import YM.FormalOPE.RG10.BlockGauge.Assembly
/-!
 # Inversion incidence

 Incidence maps project to vertex orbits, spinning uses existing liftLinks convention (with even condition for actual configurations).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Topology Function MeasureTheory PertExtension PertExtension.Orb Lattice RG
open InversionWard Push.Loops
open scoped Classical Topology ContDiff
variable {G:Gauge}
abbrev Vertex (n:Side):={x:Site n// Orb.vertex x=x}
variable {n c f:Side}
instance : Zero (Vertex n):=⟨⟨0,vertex_zero⟩⟩
 def track (x:Site n) : Vertex n:=⟨vertex x,vertex_vertex _⟩
@[simp] lemma track_hit (x : Vertex n) : track x.val=x:= Subtype.ext x.property
@[simp] lemma track_zero : track (0:Site n)=0 := Subtype.ext vertex_zero
@[simp] lemma track_neg (x:Site n) : track (-x)=track x:= Subtype.ext (vertex_neg _)
lemma touch (u : Vertex n) : u.val=0 ↔ u=0:= ⟨fun h=> Subtype.ext h,fun h=> congr_arg (fun q:Vertex n=> q.val) h⟩
lemma track_even (g : Vertex n → G.El) : evenAt (g ∘ track):= by intro i; simp

 def rim (n:Side) : Loom (Vertex n) (OEdge n) where
 origin := 0
 fromEdge e:= track e.val.1
 toEdge e:= track (e.val.1+step e.val.2)
lemma rimFrom (x : Site n)(u : Step):
 ((rim n).fromEdge (index (u.used x))=track x ∧ (rim n).toEdge (index (u.used x))=track (x+u.vec)) ∨
 ((rim n).toEdge (index (u.used x))=track x ∧ (rim n).fromEdge (index (u.used x))=track (x+u.vec)):= by
 cases u with
 | mk i u =>
   cases u
   · dsimp only [rim,index]
     rcases eR_spec ((⟨i,false⟩ : Step).used x) with h|h <;> rw [h]<;> simp [reflect, Step.used, Step.vec, sub_eq_add_neg]
     right; rw [show -x+ -step i= -(x+step i) by abel,track_neg]
   dsimp only [rim,index]
   rcases eR_spec ((⟨i,true⟩ : Step).used x) with h|h <;> rw [h]<;> simp [reflect, Step.used, Step.vec, sub_eq_add_neg]
   left; rw [show -x+step i= -(x+ -step i) by abel,track_neg]
lemma spin_agrees (g : Vertex n→ G.El)(u:LinkFrame G n) :
 (rim n).spin g u=even_spin (g ∘ track) u:= by ext1 i; simp only [even_spin,rim,Loom.spin,Lattice.gauge,lift_at]; rfl
-- canonical origin truss for one layer. Implements EXACT accepted PertExtension tree.
 def staple (n:Side) : (rim n).Truss where
 height x:=depth x.val
 parent v _:= track (v.val+(move v.val).vec)
 wire v _:= picked v.val
 descend v h:= by
  change depth (vertex _)<_; rw [depth_vertex]; exact move_falls (h ∘ (touch _).mp) -- False ∘ ?
 orientation v _:= by
  rcases rimFrom v.val (move v.val) with ⟨h,k⟩ | ⟨h,k⟩
  · exact Or.inr ⟨h.trans (track_hit _),k⟩
  exact Or.inl ⟨k,h.trans (track_hit _)⟩
lemma same_staple (i:OEdge n) : (staple n).Branch i ↔ Orb.Branch i := by
 constructor
 · rintro ⟨v,h,rfl⟩; exact ⟨v.val,fun e=>h ((touch v).mp e),rfl⟩
 rintro ⟨v,h,rfl⟩; exact ⟨track v,fun hh=> h (vertex_eq_iff.mp ((touch _).mpr hh)),(picked_rep v).symm⟩

-- projection of vertex from embedded root
 def placement (a : Ratio c f) (i:Vertex c) : Vertex f:= track (a.embed i.val)
lemma place_track (a : Ratio c f)(x:Site c): placement a (track x) = track (a.embed x):= by
 change track (a.embed (vertex x))= _; rcases vertex_spec x with h|h
 · rw [h]
 rw [h,show a.embed (-x)= -a.embed x from map_neg a.root x, track_neg]
lemma place_zero (a:Ratio c f): placement a 0=0:= by rw [←track_zero, place_track,(show a.embed 0=0 from map_zero a.root),track_zero]
lemma place_inj (a:Ratio c f): Function.Injective (placement a) := by
 intro x y h; have he: vertex (a.embed x.val)=vertex (a.embed y.val):= congr_arg (fun c: Vertex f=> c.val) h
 rcases vertex_spec (a.embed x.val) with hx|hx <;> rcases vertex_spec (a.embed y.val) with hy|hy <;> rw [hx,hy] at he
 · exact Subtype.ext (a.embed_injective he)
 · have hw: x.val= -y.val:= a.embed_injective (he.trans (map_neg a.root _).symm)
   exact (track_hit _).symm.trans ((congr_arg track hw).trans ((track_neg _).trans (track_hit _)))
 · have hw: -x.val= y.val:= a.embed_injective ((map_neg a.root _).trans he)
   exact (track_hit _).symm.trans ((track_neg _).symm.trans ((congr_arg track hw).trans (track_hit _)))
 exact Subtype.ext (a.embed_injective (neg_inj.mp he))
lemma placement_spin (g:Vertex f→G.El)(a:Ratio c f) (u:LinkFrame G c) :
 (rim c).spin (g ∘ placement a) u=even_spin (g ∘ track ∘ a.embed) u:= by
 rw [spin_agrees, show ((g ∘ placement a) ∘ track)= _ from funext (fun x=> congr_arg g (place_track a x))]
 rfl
end YM.FormalOPE.RG10.BlockGauge

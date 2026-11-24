import YM.FormalOPE.RG10.BlockGauge.Fabric
import YM.Tree.Pines
/-!
 # choice of interior inversion-compatible gauge via height minimization on actual blocks

 Patch ratio odd. Given ANY (even nonsymmetric) actual `Tree.Forest`
 on a period (not the changing-size physical tori!), construct an auxiliary inversion
 quotient forest/truss for diagram evaluations on that period in the hierarchy. **Not** claiming
 that this is literally the projection of the union of all the tree edges. Use heights to determine which
 representative to use. Does not identify any paint/root data on physical lattice (not this regulator).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Topology Function MeasureTheory PertExtension PertExtension.Orb Lattice RG
open InversionWard Push.Loops
open scoped Classical Topology ContDiff
variable {G:Gauge} {c f : Side}
namespace Fabric
-- intrinsic subset forest with block ancestry pin
 def ancestral (g : Ratio c f) (v:Vertex f): Vertex c:= track (g.parent v.val)
variable {R:Ratio c f}(h:Odd R.count.val)
include h in
lemma ancestral_track (x: Site f) : ancestral R (track x)=track (R.parent x):= by
 change track (R.parent (vertex x))= _; rcases vertex_spec x with hi | hi
 · rw [hi]
 rw [hi,show R.parent (-x)= -R.parent x from R.parent_signed h _ inversion, track_neg]
include h in
lemma ancestor (v:Vertex c) : ancestral R (placement R v)= v:= by unfold placement; rw [ancestral_track h,R.embed_parent,track_hit]
 def planted (R:Ratio c f) (v:Vertex f) := placement R (ancestral R v) = v

structure Inside (g:Ratio c f) where
 height : Vertex f → ℕ
 bound (v): height v≤4*g.count.val
 wire (v) (h:¬planted g v) : OEdge f
 up (v) (h:¬planted g v) : Vertex f
 descend (v)(h:¬planted g v): height (up v h)<height v
 stay (v)(h:¬planted g v) : ancestral g (up v h)=ancestral g v
 orientation (v)(h:¬planted g v) : ((rim f).fromEdge (wire v h) = up v h ∧ (rim f).toEdge (wire v h)=v) ∨ ((rim f).toEdge (wire v h) = up v h ∧ (rim f).fromEdge (wire v h)=v)

namespace Inside
variable (T:Tree.Forest R)
 def closer (v: Vertex f) : Site f := if T.height v.val ≤ T.height (-v.val) then v.val else -v.val
@[simp] lemma closer_id (v:Vertex f): track (closer T v)=v:=by unfold closer; split<;>simp
lemma close_bound (v:Vertex f): T.height (closer T v) ≤ 4 * R.count.val:= T.bound _
lemma rank_min (x:Site f): T.height (closer T (track x)) ≤ T.height x:= by
 unfold closer; change T.height (if T.height (vertex x) ≤ T.height (-vertex x) then vertex x else -vertex x) ≤ T.height x
 rcases vertex_spec x with e|e <;> rw [e] <;> split
 · exact le_rfl
 · exact Nat.le_of_not_le (by assumption)
 · rename_i hw; simpa only [neg_neg] using hw
 simp
include h in
lemma starts (x:Site f) (hx: ¬planted R (track x)): Tree.leaf R x:= by
 intro hg; apply hx
 change x = R.embed (R.parent x) at hg
 unfold planted; rw [ancestral_track h,place_track,hg.symm]
include h in
lemma close_leaf (v:Vertex f)(hv:¬planted R v) : Tree.leaf R (closer T v):= starts h _ (by simpa)

 def project : Inside R where
 height v:= T.height (closer T v)
 wire v _ := index ((T.up (closer T v)).used (closer T v))
 up v _ := track (closer T v+(T.up (closer T v)).vec)
 bound:=close_bound _
 descend _ hv:= lt_of_le_of_lt (rank_min T _) (T.rise _ (close_leaf h T _ hv))
 stay v hv:= by
  rw [ancestral_track h,T.stays _ (close_leaf h T v hv), ← ancestral_track h,closer_id]
 orientation v _:= by
  rcases rimFrom (closer T v) (T.up (closer T v)) with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> first
    | exact Or.inr ⟨hb,ha.trans (closer_id T v)⟩
    | exact Or.inl ⟨hb,ha.trans (closer_id T v)⟩
-- project uses h parameter maybe implicit?
end Inside
end Fabric
end YM.FormalOPE.RG10.BlockGauge

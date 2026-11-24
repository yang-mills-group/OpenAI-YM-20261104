import YM.FormalOPE.RG10.BlockGauge.Graft
/-!
 # hierarchy respecting gauge

 No proposition that the real lattice employs any of these, or has posts.
 Resolution is on the inversion auxiliary graph. Any hierarchical gauge will
 be produced by `Cloth`; grammar saturates all inside choices plus any maximal
 tree choice on terminal slice. No stationarity estimate here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Topology Function MeasureTheory PertExtension PertExtension.Orb Lattice RG
open InversionWard Push.Loops
open scoped Classical Topology ContDiff
variable {G:Gauge} {c f n : Side}
namespace Fabric
variable {L:Fabric G c} {S:StepData c f} {H:S.patch.Branches S.kernel G}{t:S.Choices}{hf:_root_.Even f.val}
namespace Inside
variable (P : Inside (S.ratio))(T:L.loom.Truss)
-- bundle h.Proof orientation. Height lex via successor.
private lemma lift_ne {v : Vertex f}(h: planted (S.ratio) v) (hv:v≠0) : ancestral (S.ratio) v≠ (0:Vertex c):= by
 intro hp; apply hv; rw [← h,hp,place_zero]
private lemma odd : Odd (S.ratio.count.val):= S.patch.odd_side
-- `lift_ne` origin of loom = 0
def nextRoot {v:Vertex f} (h: v≠0)(m:planted (S.ratio) v) := placement (S.ratio) (T.parent (ancestral (S.ratio) v) (show ancestral (S.ratio) v≠ _ from lift_ne m h))
def altitude (v:Vertex f) := (T.height (ancestral (S.ratio) v))*(4*S.patch.L.val+1) + P.height v
def join (H:S.patch.Branches S.kernel G)(t:S.Choices)(hf:_root_.Even f.val) : (layer S H t hf L).loom.Truss where
 height:= P.altitude T -- note variable implicit order?
 parent v h:= if m:planted (S.ratio) v then nextRoot T h m else P.up _ m
 wire v h:= if m:planted (S.ratio) v then .inr (T.wire (ancestral (S.ratio) v) (lift_ne m h)) else .inl (P.wire _ m)
 descend v h:= by
  split
  · rename_i m
    unfold altitude nextRoot; rw [ancestor (odd (S:=S))]
    set x:= ancestral (S.ratio) v; set y:=T.parent _ _
    have ha : T.height y < T.height x:= T.descend _ _
    have hh:P.height (placement (S.ratio) y) ≤ 4*S.patch.L.val:= P.bound _
    have he:= Nat.mul_le_mul_right (4*S.patch.L.val+1) (show T.height y + 1≤ T.height x from ha)
    rw [Nat.add_mul,one_mul] at he
    change T.height y* _ + _ < T.height x* _ + _
    omega
  rename_i m
  unfold altitude; rw [P.stay]; exact Nat.add_lt_add_left (P.descend v m) _
 orientation v h := by
  split <;> rename_i m
  · -- pos
    rcases T.orientation (ancestral (S.ratio) v) (lift_ne m h) with ⟨a,b⟩|⟨a,b⟩
    · exact Or.inl ⟨congr_arg (placement _) a,(congr_arg (placement _) b).trans m⟩
    exact Or.inr ⟨(congr_arg (placement _) a).trans m,congr_arg (placement _) b⟩
  exact (P.orientation _ m).imp id And.symm
-- Branch characterization
def Innate (i : OEdge f):= ∃ (v:Vertex f)(m:¬planted (S.ratio) v), P.wire v m=i
private lemma placed_root (v:Vertex c) : planted (S.ratio) (placement (S.ratio) v):= congr_arg _ (ancestor odd v)
variable (H t hf)
lemma inner_only (i:OEdge f): (P.join T H t hf).Branch (.inl i) ↔ P.Innate i:= by
 constructor
 · rintro ⟨v,hv,h⟩; unfold join at h; dsimp only at h; split at h
   · simp at h
   rename_i m; exact ⟨v,m,Sum.inl.inj h⟩
 rintro ⟨v,m,h⟩; refine ⟨v,?_⟩
 have he: v ≠ 0:= by
  intro e; apply m
  rw [e,←place_zero]; exact placed_root 0
 exact ⟨he,by unfold join; dsimp only; rw [dif_neg m,h]⟩
lemma outer_only (i:L.Path): (P.join T H t hf).Branch (.inr i) ↔ T.Branch i:= by
 constructor
 · rintro ⟨v,hv,h⟩; unfold join at h; dsimp only at h; split at h
   · rename_i m; exact ⟨_,lift_ne m hv,Sum.inr.inj h⟩
   simp at h
 rintro ⟨v,m,h⟩; have hm:= placed_root (S:=S) v; have he: placement (S.ratio) v ≠ 0:= fun e=> m (place_inj _ (e.trans (place_zero _).symm))
 refine ⟨_,he,?_⟩; unfold join; dsimp only; rw [dif_pos hm]; congr 1
   -- dep
 try rw [← h]; congr 1; exact ancestor odd v
end Inside

-- All steps choices in order, no floor stripping. Can pick from actual-supplied odd stats.
inductive Cloth : {n:Side}→ Fabric G n → Type
| floor (n:Side)(h:_root_.Even n.val) (T:(Fabric.endcap (G:=G) n h).loom.Truss) : Cloth (.endcap n h)
| inLayer {c f:Side}{S:StepData c f}{b:S.patch.Branches S.kernel G}{t:S.Choices}{h:_root_.Even f.val}{L: Fabric G c} (T:Inside S.ratio)(C:Cloth L): Cloth (.layer S b t h L)
 def Cloth.choose {n: Side}{L:Fabric G n}: Cloth L→ L.loom.Truss
 | .floor _ _ T=>T
 | .inLayer T C=> T.join (choose C) _ _ _
 def localTruss {n:Side} (L:Fabric G n) : Cloth L := match L with
 | .endcap n h=> .floor n h (Fabric.endcap (G:=G) n h).atop
 | .layer S _ _ _ L => .inLayer (Inside.project (R:= S.ratio) S.patch.odd_side (Classical.choice (Tree.select S.ratio S.patch.odd_side))) (localTruss L)
end Fabric
end YM.FormalOPE.RG10.BlockGauge

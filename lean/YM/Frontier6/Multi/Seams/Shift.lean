import YM.Push.RELAY_DIFFERENCE.Placement
import YM.Push.GRID_APPROXIMATION.Translate
import YM.Frontier6.Pair.Marginal

/-! Offset & orientation freedom of a rooted price, no spectator in the stamp. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Platform
open Function Filter Set Lattice MeasureTheory Wilson Extraction Cells Push
open scoped Topology BigOperators Classical
variable {G:Gauge}{S:Schedule}{m N k p n:ℕ}
variable {C:Family G}
lemma move_zero {n:Side}(b c:Site n)(x:Config G n):Lattice.translate b (Lattice.translate c x) = Lattice.translate (b+c) x:=by funext U; simp [Lattice.translate,add_assoc]
lemma move_allow {n:Side} (F:Config G n→ℂ): RelayDifference.literal (fun x=>F ∘ Lattice.translate x):=fun a b=>funext fun c=>congr_arg F (move_zero ..).symm

section
variable (S:Schedule)
lemma frameShift (he : m ≤ N) {y:Site (S.side N p)} (v:Site (S.side m p))
    (h:y∈(center S p he 0).margin v n): y-(S.toDepth he p).embed v ∈ (center S p he 0).margin 0 n:= by
   let T:=center S p he 0; let x:= y-(S.toDepth he p).embed v
   have he(i): T.coordinated 0 x i=T.coordinated v y i:=by unfold Tiling.coordinated; rw [T.starts_zero]; congr 1; change y i - T.units.root v i-_= y i-(T.base i+T.units.root v i); abel
   change x∈ T.chamber 0 ∧ ∀ a,_; refine ⟨fun i=>?_,fun i=>?_⟩; swap; · change n ≤ T.coordinated 0 x i ∧ _; rw [he i]; exact h.2 i
   change T.kind.Strict _ (T.coordinated 0 x i); rw [he i]
   exact h.1 i
end

section
local notation "X"=> C.side N p
set_option quotPrecheck false
variable (h:C.Makes)
include h
lemma last_path (T:Tiling X) {x:Site X}(hk:k≤N) {G':Config G (C.side N p)→ℂ} {B:ℝ}
   (hT:Interior ((center C.S p hk 0).chamber 0) G')(hp:(center C.S p hk 0).rootTest (C.beta N p) G' ≤ B)
   (ho:x∈T.margin 0 (3*Cells.span C.S hk p))(hi:Cells.span C.S hk p∣ T.side.val) :
     Interior (T.chamber 0) (G' ∘ Lattice.translate x)∧ T.rootTest (C.beta N p) (G' ∘ Lattice.translate x) ≤ B:=by
   have he : G' ∘ Lattice.translate 0=G':=funext (fun i=>congr_arg G' (by funext u;simp [Lattice.translate]))
   exact RelayDifference.offset hk T _ _ hi (move_allow G') (seamless h ..) (he.symm ▸ hT) (he.symm ▸ hp) ho

lemma moved_basis (hk:k≤ N)(hb:m ≤ k) {x: Site X} (v:Site (C.side m p)) {F: Config G (C.side N p)→ℂ} {B:ℝ}
   (hf:Interior ((center C.S p hk 0).chamber 0) F)(hp:(center C.S p hk 0).rootTest (C.beta N p) F ≤ B)(he:x∈(center C.S p (hb.trans hk) 0).margin v (3*Cells.span C.S hk p)) :
   let T:=center C.S p (hb.trans hk) 0
   ∃ G', Interior (T.chamber 0) G' ∧ T.rootTest (C.beta N p) G' ≤ B ∧ T.copy v G'=F ∘ Lattice.translate x:=by
   let u:= (C.S.toDepth (hb.trans hk) p).embed v; let y:= x-u; intro T
   obtain ⟨hu,hU⟩:= last_path h T hk hf hp (frameShift C.S (hb.trans hk) v he) (Around.inherits (C:=C) hb hk)
   obtain ⟨G',hG,hH,hV⟩:= GridApprox.source_for_translate C.S (hb.trans hk) v (F ∘ Lattice.translate y) hu (C.beta N p)
   refine ⟨G',hH, hV.le.trans hU,?_⟩; change (GridApprox.tilesAt C.S p _).copy v G'=_; rw [hG]; funext U; unfold Function.comp; rw [move_zero, show y+GridApprox.anchor C.S p _ v=x from sub_add_cancel ..]
end
end YM.Frontier6.Platform
